module main(clk,led);
	input clk;
   wire clock;
	reg reset_n;
	wire Branch_Zero,PCWrite;
	wire [1:0] ForwardA_ALU,ForwardB_ALU,ForwardA_EQ,ForwardB_EQ;
	wire [2:0] ALUOp_ID,ALUOp_EX,ALUcontrol;
	wire [4:0] mux_RegDST_EX,mux_RegDST_WB,mux_RegDST_MEM;
	wire [9:0] Ctrl_Code;
	wire [31:0] PC_4_IF,PC_Offset,mux_Branch,pc,Instr_IF,PC_4_ID,Instr_ID,Rs_Data_ID;
	wire [31:0] Rt_Data_ID,Offset,mux_MemtoReg,Immediate_ID,Immediate_EX,Instr_EX;
	wire [31:0] mux_ALUSrc,Rs_Data_EX,Rt_Data_EX,ALUResult_MEM,muxA_ALUsrc,muxB_ALUsrc,ALUResult_EX;
	wire [31:0] muxA_EQsrc,muxB_EQsrc,Rt_Data_MEM,MemData_MEM,MemData_WB,ALUResult_WB;
	wire IFIDWrite,Stall,RegDST_ID,Branch,MemRead_ID,MemtoReg_ID,MemWrite_ID,ALUSrc_ID,RegWrite_ID;
	wire Branch_Taken,RegWrite_EX,MemtoReg_EX;
	wire MemRead_EX,MemWrite_EX,ALUSrc_EX,RegDST_EX,Zero,RegWrite_MEM,MemtoReg_MEM;
	wire MemRead_MEM,MemWrite_MEM,RegWrite_WB,MemtoReg_WB;
       
        output [10:0]led;
	assign led[0] =PCWrite;
   assign led[1] =Branch_Zero;
	assign led[2] =RegWrite_WB;
	assign led[3] =ForwardA_ALU;
	assign led[4] =MemRead_ID;
	assign led[5] =Branch_Taken;
   assign led[6] =RegWrite_EX;        
	assign led[7] =MemtoReg_ID;
	assign led[8] =MemtoReg_EX;
	assign led[9] =clock;
	assign led[10]=ALUResult_EX;
       
	divisorFrequencia divisorFrequencia(clk, clock);
	MUX2x32 MUXBranch(.Data0(PC_4_IF),.Data1(PC_Offset),.select(Branch_Zero),.Data_out(mux_Branch));
	MUX10 ControlStall(.Data1(10'b0),.Data2(Ctrl_Code),.select_in(Stall),.Data_out({RegDST_ID,Branch,MemRead_ID,MemtoReg_ID,ALUOp_ID,MemWrite_ID,ALUSrc_ID,RegWrite_ID}));
	MUX3x32 MUX1EQ(.Data0(Rs_Data_ID),.Data1(mux_MemtoReg),.Data2(ALUResult_MEM),.select(ForwardA_ALU),.Data_out(muxA_EQsrc));
	MUX3x32 MUX2EQ(.Data0(Rt_Data_ID),.Data1(mux_MemtoReg),.Data2(ALUResult_MEM),.select(ForwardB_ALU),.Data_out(muxB_EQsrc));
	MUX5 MUXRegDst(.Data1(Instr_EX[20:16]),.Data2(Instr_EX[15:11]),.select(RegDST_EX),.Data_out(mux_RegDST_EX));
	MUX2x32 MUXALUSrc(.Data0(muxB_ALUsrc),.Data1(Immediate_EX),.select(ALUSrc_EX),.Data_out(mux_ALUSrc));
	MUX3x32 MUX1ALU(.Data0(Rs_Data_EX),.Data1(mux_MemtoReg),.Data2(ALUResult_MEM),.select(ForwardA_ALU),.Data_out(muxA_ALUsrc));
	MUX3x32 MUX2ALU(.Data0(Rt_Data_EX),.Data1(mux_MemtoReg),.Data2(ALUResult_MEM),.select(ForwardB_ALU),.Data_out(muxB_ALUsrc));
	MUX2x32 MUXMemtoReg(.Data0(ALUResult_WB),.Data1(MemData_WB),.select(MemtoReg_WB),.Data_out(mux_MemtoReg));
	
	
	ALUcontrol ALUcontrol_test(.funct(Immediate_EX[5:0]),.ALUOp(ALUOp_EX),.ALUcontrol(ALUcontrol));
	ALU ALU_test(.Data1(muxA_ALUsrc),.Data2(mux_ALUSrc),.ALUcontrol(ALUcontrol),.Data(ALUResult_EX),.Zero(Zero));
	Add Add_test(.Data1(pc),.Data2(32'd4),.Data_out(PC_4_IF));
	AndPort And_test(.entrada1(muxA_EQsrc),.entrada2(muxB_EQsrc),.result(Branch_Taken));
	Add PC_Add_Offset(.Data1(PC_4_ID),.Data2(Offset),.Data_out(PC_Offset));
	Control Control_test(.OpCode(Instr_ID[31:26]),.RegDst(Ctrl_Code[9]),.Branch(Ctrl_Code[8]),.MemRead(Ctrl_Code[7]),.MemtoReg(Ctrl_Code[6]),.ALUOp(Ctrl_Code[5:3]),.MemWrite(Ctrl_Code[2]),.ALUSrc(Ctrl_Code[1]),.RegWrite(Ctrl_Code[0]));
	DataMemory DataMemory_test(.clock(clock),.addr(ALUResult_MEM),.Data_in(Rt_Data_MEM),.MemRead(MemRead_MEM),.MemWrite(MemWrite_MEM),.Data_out(MemData_MEM));
	InstructionMemory InstructionMemory_test(pc,Instr_IF,clock);
	IFID IFID_test(.clock(clock),.rst(reset_n),.PC_4_in(PC_4_IF),.instr_in(Instr_IF),.hazard_in(~Stall),.flush_in(Branch_Zero),.PC_4_out(PC_4_ID),.instr_out(Instr_ID));
	Registers Registers_test(.clock(clock),.Rs_addr(Instr_ID[25:21]),.Rt_addr(Instr_ID[20:16]),.Rd_addr(mux_RegDST_WB),.Rd_Data(mux_MemtoReg),.RegWrite(RegWrite_WB), .Rs_Data(Rs_Data_ID),.Rt_Data(Rt_Data_ID));
	SignedExtend SignedExtend_test(.Data_in(Instr_ID[15:0]),.Data_out(Immediate_ID));
	Forwarding Forwarding_test(.IfIdRegRs(Instr_ID[25:21]),.IfIdRegRt(Instr_ID[20:16]),.IdExRegRs(Instr_EX[25:21]),.IdExRegRt(Instr_EX[20:16]),.ExMemRegWrite(RegWrite_MEM),
			.ExMemRegRd(mux_RegDST_MEM),.MemWbRegWrite(RegWrite_WB),.MemWbRegRd(mux_RegDST_WB),.Branch(Branch),.ForwardA_ALU(ForwardA_ALU),.ForwardB_ALU(ForwardB_ALU),
			.ForwardA_EQ(ForwardA_EQ),.ForwardB_EQ(ForwardB_EQ));
	HazardDetection HazardDetection_test(.IFIDRegRs(Instr_ID[25:21]),.IFIDRegRt(Instr_ID[20:16]),.IDEXMemRead(MemRead_EX),.IDEXRegDST(mux_RegDST_EX),.Branch(Ctrl_Code[8]),.IDEXRegWrite(RegWrite_EX),.Stall(Stall),.clock(clock));
	PC PC(.clock(clock),.reset_n(reset_n),.PCin(mux_Branch),.PCout(pc),.pcWrite(~Stall));
	IDEX IDEX(.clock(clock),.rst(reset_n),.RegWrite_in(RegWrite_ID),.MemtoReg_in(MemtoReg_ID),.MemRead_in(MemRead_ID),.MemWrite_in(MemWrite_ID),.ALUSrc_in(ALUSrc_ID),
			.ALUOp_in(ALUOp_ID),.RegDst_in(RegDST_ID),.RegRsData_in(Rs_Data_ID),.RegRtData_in(Rt_Data_ID),.Immediate_in(Immediate_ID),.instr_Rs_addr_in(Instr_ID[25:21]),
			.instr_Rt_addr_in(Instr_ID[20:16]),.instr_Rd_addr_in(Instr_ID[15:11]),.RegWrite_out(RegWrite_EX),.MemtoReg_out(MemtoReg_EX),.MemRead_out(MemRead_EX),
			.MemWrite_out(MemWrite_EX),.ALUSrc_out(ALUSrc_EX),.ALUOp_out(ALUOp_EX),.RegDst_out(RegDST_EX),.RegRsData_out(Rs_Data_EX),.RegRtData_out(Rt_Data_EX),
			.Immediate_out(Immediate_EX),.instr_Rs_addr_out(Instr_EX[25:21]),.instr_Rt_addr_out(Instr_EX[20:16]),.instr_Rd_addr_out(Instr_EX[15:11]));
	
	EX_MEM EX_MEM_test(.clock(clock),.rst(reset_n),.RegWrite_in(RegWrite_EX),.MemtoReg_in(MemtoReg_EX),.MemRead_in(MemRead_EX),.MemWrite_in(MemWrite_EX),.ALUData_in(ALUResult_EX),
			.MemWriteData_in(muxB_ALUsrc),.WBregister_in(mux_RegDST_EX),.RegWrite_out(RegWrite_MEM),.MemtoReg_out(MemtoReg_MEM),.MemRead_out(MemRead_MEM),
			.MemWrite_out(MemWrite_MEM),.ALUData_out(ALUResult_MEM),.MemWriteData_out(Rt_Data_MEM),.WBregister_out(mux_RegDST_MEM));
	MEMWB MEMWB_test(.clock(clock),.rst(reset_n),.RegWrite_in(RegWrite_MEM),.MemtoReg_in(MemtoReg_MEM),.MemData_in(MemData_MEM),.ALUData_in(ALUResult_MEM),.WBregister_in(mux_RegDST_MEM),
			.RegWrite_out(RegWrite_WB),.MemtoReg_out(MemtoReg_WB),.MemData_out(MemData_WB),.ALUData_out(ALUResult_WB),.WBregister_out(mux_RegDST_WB));
	
	
	assign Offset=Immediate_ID << 2;
	assign Branch_Zero=Branch & Branch_Taken;
	
	
endmodule

module divisorFrequencia (input wire clk, output reg clock = 0);

	reg [31:0] cont = 0;

	always @ (posedge clk)
	begin
		cont = cont + 1;
		
		if(cont == 50000000)
		begin
			clock = ~clock;
			cont = 0;
		end
	end

endmodule

module Control(OpCode, RegDst, Branch, MemRead, MemtoReg, ALUOp, MemWrite, ALUSrc, RegWrite);
	input [5:0] OpCode;
	output RegDst,Branch,MemRead,MemtoReg,MemWrite,ALUSrc,RegWrite;
	output [2:0] ALUOp;
	reg [9:0] out;
   
	assign RegDst = out[9];
	assign Branch = out[8];
	assign MemRead = out[7];
	assign MemtoReg = out[6];
	assign MemWrite = out[5];
	assign ALUSrc = out[4];
	assign RegWrite = out[3];
	assign ALUOp = out[2:0];
   
	always @(OpCode)
		case(OpCode)
			6'b000000: //TIPO R
				out = 10'b1000001100;
			6'b001000: //TIPO Addi
				out = 10'b0000011010;
			6'b001100: //TIPO  Andi
				out = 10'b0000011000;
			6'b001101: //TIPO ORi
				out = 10'b0000011001;
			6'b101011: //TIPO SW
				out = 10'b0000110010;
			6'b100011: //TIPO LW
				out = 10'b0011011010;
			6'b000100: //TIPO BEQ
				out = 10'b0100000011;
		endcase 
endmodule

module ALU(Data1, Data2, ALUcontrol, Data, Zero);
	input [31:0] Data1,Data2;
	input [2:0] ALUcontrol;
	output [31:0] Data;
	output Zero;
	reg [31:0] Data;
	reg Zero;

	always @(Data1 or Data2 or ALUcontrol)begin
	if (~ALUcontrol[2] & ALUcontrol[1] & ~ALUcontrol[0])begin
		Data = Data1 + Data2;
		if (Data == 32'b0)begin
			Zero = 1'b1;
		end
		else begin
			Zero = 1'b0;
		end
	end
	if (ALUcontrol[2] & ALUcontrol[1] & ~ALUcontrol[0])begin
		Data = Data1 - Data2;
		if (Data == 32'b0)begin
			Zero = 1'b1;
		end
		else begin
			Zero = 1'b0;
		end
	end
	if (~ALUcontrol[2] & ~ALUcontrol[1] & ~ALUcontrol[0])begin
		Data = Data1 & Data2;
		if (Data == 32'b0)begin
			Zero = 1'b1;
		end
		else begin
			Zero = 1'b0;
		end
	end
	if (~ALUcontrol[2] & ~ALUcontrol[1] & ALUcontrol[0])begin
		Data = Data1 | Data2;
		if (Data == 32'b0)begin
			Zero = 1'b1;
		end
		else begin
			Zero = 1'b0;
		end
	end
	if (ALUcontrol[2] & ALUcontrol[1] & ALUcontrol[0])begin
		if ((Data1 - Data2) < 0)begin
			Data = 32'b1;
		end
		else begin
			Data = 32'b0;
		end
	end
	end
endmodule

module Add(Data1, Data2, Data_out);
	input [31:0] Data1,Data2;
	output [31:0] Data_out;
	reg [31:0] Data_out;

	always @(Data1 or Data2)begin
		Data_out = Data1 + Data2;
	end
endmodule

module ALUcontrol(funct, ALUOp, ALUcontrol);
	input [5:0] funct;
	input [2:0] ALUOp;
	output [2:0] ALUcontrol;
	reg [2:0] ALUcontrol;

	always @(ALUOp or funct)
    case(ALUOp)
		3'b010:
			ALUcontrol = 3'b010; // LW, SW , ADDI, ADD
		3'b011:
			ALUcontrol = 3'b110; // BEQ, SUB
		3'b000:
			ALUcontrol = 3'b000; // AND ANDI
		3'b001:
			ALUcontrol = 3'b001; // OR, ORI
		3'b100:
	case(funct)
		6'b100000:
			ALUcontrol = 3'b010; // ADD
		6'b100010:
			ALUcontrol = 3'b110; // SUB
		6'b100100:
			ALUcontrol = 3'b000; // AND
		6'b100101:
			ALUcontrol = 3'b001; // OR 
		6'b101010:
			ALUcontrol = 3'b111; // SLT
	endcase 
    endcase 
endmodule

module DataMemory(clock, addr, Data_in, MemRead, MemWrite, Data_out);
	input MemWrite,MemRead, clock;
	input[31:0]addr,Data_in;
	output reg[31:0]Data_out;
	reg[31:0]Memory[256:0];
        initial begin
		Memory[0] = 32'b00000000000000000000000000000001;
		Memory[1] = 32'b00000000000000000000000000000011;
		Memory[2] = 32'b00000000000000000000000000000111;
		Memory[3] = 32'b00000000000000000000000000000010;
		Memory[4] = 32'b00000000000000000000000000000000;
		Memory[5] = 32'b00000000000000000000000000000000;
		Memory[6] = 32'b00000000000000000000000000000000;
      Memory[7] = 32'b00000000000000000000000000000000;
		Memory[8] = 32'b00000000000000000000000000000000;
		Memory[9] = 32'b00000000000000000000000000000000;
		Memory[10] = 32'b00000000000000000000000000000000;
		Memory[11] = 32'b00000000000000000000000000000000;
		Memory[12] = 32'b00000000000000000000000000000000;
		Memory[13] = 32'b00000000000000000000000000000000;
	end

	always @(negedge clock) begin
        if(MemWrite)
        	Memory[addr] <= Data_in;
        if(MemRead)
		Data_out <= Memory[addr];
	end
endmodule

module AndPort(entrada1, entrada2, result);
	input [31:0] entrada1,entrada2;
	output result;

	assign result = (entrada1 == entrada2) ? 1 : 0 ;
endmodule

module MUX2x32(Data0,Data1,select,Data_out);
	input [31:0] Data0,Data1;
	input select;
	output [31:0] Data_out;
	assign Data_out = (select) ? Data1 : Data0;
endmodule

module MUX3x32(Data0,Data1,Data2,select,Data_out);
	input [31:0] Data0,Data1,Data2;
	input [1:0] select;
	output [31:0] Data_out;
	assign Data_out = (select[1]) ? Data2 : ((select[0]) ? Data1 : Data0);
endmodule

module MUX5(Data1,Data2,select,Data_out);
	input [4:0] Data1,Data2;
	input select;
	output [4:0] Data_out;
	assign Data_out = (select) ? Data2 : Data1;
endmodule

module MUX10(Data1, Data2, select_in, Data_out);
	input [9:0] Data1,Data2;
	input select_in;
	output [9:0] Data_out;
	assign Data_out = (select_in) ? Data1 : Data2;
endmodule

module PC(clock,reset_n,PCin,PCout,pcWrite);
	input clock,reset_n,pcWrite;
	input [31:0] PCin;
	output [31:0] PCout;
	reg [31:0] PCout;

	always @(posedge clock or negedge reset_n)begin
		if(~reset_n)begin
			PCout<=32'b0;
		end
		else if(pcWrite)begin
			PCout<=PCin;
		end
	end
endmodule

module Registers (clock,Rs_addr,Rt_addr,Rd_addr,Rd_Data,RegWrite,Rs_Data,Rt_Data);
	input clock,RegWrite;
	input [4:0] Rs_addr,Rt_addr,Rd_addr;
	input [31:0] Rd_Data;
	output [31:0] Rs_Data,Rt_Data;

	reg [31:0] RegistersMemory [0:31];
	initial begin
		RegistersMemory[0] = 32'b00000000000000000000000000000001;
		RegistersMemory[1] = 32'b00000000000000000000000000000001;
		RegistersMemory[2] = 32'b00000000000000000000000000000010;
		RegistersMemory[3] = 32'b00000000000000000000000000000001;
		RegistersMemory[4] = 32'b00000000000000000000000000000000;
		RegistersMemory[5] = 32'b00000000000000000000000000000001;
      RegistersMemory[6] = 32'b00000000000000000000000000000000;
		RegistersMemory[7] = 32'b00000000000000000000000000000001;		
      RegistersMemory[8] = 32'b00000000000000000000000000000101; //T0 = 5
      RegistersMemory[9] = 32'b00000000000000000000000000000100; //T1 = 4
		RegistersMemory[10] = 32'b0000000000000000000000000000101; //T2 = 5
		RegistersMemory[11] = 32'b0000000000000000000000000000100; //T3 = 4
		RegistersMemory[12] = 32'b00000000000000000000000000000001;
		RegistersMemory[13] = 32'b00000000000000000000000000000000;
		RegistersMemory[14] = 32'b00000000000000000000000000000001;
		RegistersMemory[15] = 32'b00000000000000000000000000000000;
      RegistersMemory[16] = 32'b00000000000000000000000000000001;
		RegistersMemory[17] = 32'b00000000000000000000000000000001;
		RegistersMemory[18] = 32'b00000000000000000000000000000010;
		RegistersMemory[19] = 32'b00000000000000000000000000000001;
		RegistersMemory[20] = 32'b00000000000000000000000000000000;
		RegistersMemory[21] = 32'b00000000000000000000000000000001;
		RegistersMemory[22] = 32'b00000000000000000000000000000000;
		RegistersMemory[23] = 32'b00000000000000000000000000000000;
		RegistersMemory[24] = 32'b00000000000000000000000000000001;
		RegistersMemory[25] = 32'b00000000000000000000000000000000;
      RegistersMemory[26] = 32'b00000000000000000000000000000001;
		RegistersMemory[27] = 32'b00000000000000000000000000000001;
		RegistersMemory[28] = 32'b00000000000000000000000000000010;
		RegistersMemory[29] = 32'b00000000000000000000000000000001;
		RegistersMemory[30] = 32'b00000000000000000000000000000000;
		RegistersMemory[31] = 32'b00000000000000000000000000000001;
	end
    
	assign Rs_Data=(Rs_addr==5'b0) ? 32'b0 : RegistersMemory[Rs_addr];
	assign Rt_Data=(Rt_addr==5'b0) ? 32'b0 : RegistersMemory[Rt_addr];

	
	always @(negedge clock)begin
		if(RegWrite)
			RegistersMemory[Rd_addr] <= Rd_Data;
	end
endmodule

module SignedExtend(Data_in,Data_out);
	input [15:0] Data_in;
	output [31:0] Data_out;

	assign Data_out = {{16{Data_in[15]}}, Data_in};
endmodule

module InstructionMemory(PCout,Instruction,clock);
	input[31:0]PCout;
        input clock;
	output reg[31:0]Instruction;
	reg[31:0]Memory[31:0];
	initial begin
		//Memory[0] = 32'b00000001010010111011000000100010; //sub
		//Memory[1] = 32'b00000001000010011010100000100000; //add
		
		Memory[0] = 32'b00000010010000000101100000100000;
		Memory[1] = 32'b00000000000100100101100000100100;
		Memory[2] = 32'b00000010010100110101100000100101;
		Memory[3] = 32'b00000010010000000101100000100010;
		Memory[4] = 32'b00000000000100100101100000101010;
		Memory[5] = 32'b10001100000000000000000000000000;
		Memory[6] = 32'b10101111101010000000000000101000;
      Memory[7] = 32'b00010000001000100000000000000100;
      
		/*
		Memory[0] = 32'b00000010010000000101100000100000;
		Memory[1] = 32'b00000000000100100101100000100100;
		*/
	end
	always @(posedge clock) begin
		Instruction=Memory[PCout/4];
	end
endmodule

/*
PIPELINE
*/

module EX_MEM(clock,rst,RegWrite_in,MemtoReg_in,MemRead_in,MemWrite_in,ALUData_in,MemWriteData_in,WBregister_in,RegWrite_out,MemtoReg_out,MemRead_out,
		MemWrite_out,ALUData_out,MemWriteData_out,WBregister_out);
	input clock,rst,RegWrite_in,MemtoReg_in,MemRead_in,MemWrite_in;
	input [31:0] ALUData_in,MemWriteData_in;
	input [4:0] WBregister_in;
	output RegWrite_out,MemtoReg_out,MemRead_out,MemWrite_out;
	output [31:0] ALUData_out,MemWriteData_out;
	output [4:0] WBregister_out;
	reg RegWrite_out,MemtoReg_out,MemRead_out,MemWrite_out;
	reg [31:0] ALUData_out,MemWriteData_out;
	reg	[4:0] WBregister_out;

	always @(posedge clock or negedge rst)begin
		if(~rst)begin
			RegWrite_out<=1'b0;
			MemtoReg_out<=1'b0;
			MemRead_out<=1'b0;
			MemWrite_out<=1'b0;
			ALUData_out<=32'b0;
			MemWriteData_out<=32'b0;
			WBregister_out<=5'b0;		
		end
		else begin
			RegWrite_out<=RegWrite_in;
			MemtoReg_out<=MemtoReg_in;
			MemRead_out<=MemRead_in;
			MemWrite_out<=MemWrite_in;
			ALUData_out<=ALUData_in;
			MemWriteData_out<=MemWriteData_in;
			WBregister_out<=WBregister_in;	
		end
	end
endmodule

module Forwarding(IfIdRegRs,IfIdRegRt,Branch,IdExRegRs,IdExRegRt,ExMemRegWrite,ExMemRegRd,MemWbRegWrite,MemWbRegRd,ForwardA_ALU,ForwardB_ALU,ForwardA_EQ,ForwardB_EQ);
	input [4:0] IdExRegRs,IdExRegRt,ExMemRegRd,MemWbRegRd,IfIdRegRs,IfIdRegRt; 
	input ExMemRegWrite,MemWbRegWrite,Branch;
	output [1:0] ForwardA_ALU,ForwardB_ALU,ForwardA_EQ,ForwardB_EQ;
	reg [1:0] ForwardA_ALU,ForwardB_ALU,ForwardA_EQ,ForwardB_EQ;

	initial begin
		ForwardA_ALU = 2'b00;
		ForwardB_ALU = 2'b00;
		ForwardA_EQ = 2'b00;
		ForwardB_EQ = 2'b00;
	end

	always @(IdExRegRs or IdExRegRt or ExMemRegRd or MemWbRegRd or IfIdRegRs or IfIdRegRt or ExMemRegWrite or MemWbRegWrite) begin
	if (ExMemRegWrite && (ExMemRegRd != 5'b0) && (ExMemRegRd == IdExRegRs)) 
		ForwardA_ALU <= 2'b10;
	else if (MemWbRegWrite && (MemWbRegRd != 5'b0) && (MemWbRegRd == IdExRegRs))
		ForwardA_ALU <= 2'b01;
	else
		ForwardA_ALU <= 2'b00;
	if (ExMemRegWrite && (ExMemRegRd != 5'b0) && (ExMemRegRd == IdExRegRt))
		ForwardB_ALU <= 2'b10;
	else if (MemWbRegWrite && (MemWbRegRd != 5'b0) && (MemWbRegRd == IdExRegRt))
		ForwardB_ALU <= 2'b01;
	else
		ForwardB_ALU <= 2'b00;
	if (Branch)begin
		if (ExMemRegWrite && (ExMemRegRd != 5'b0) && (ExMemRegRd == IfIdRegRs)) 
			ForwardA_EQ <= 2'b10;
		else if (MemWbRegWrite && (MemWbRegRd != 5'b0) && (MemWbRegRd == IfIdRegRs))
			ForwardA_EQ <= 2'b01;
		else
			ForwardA_EQ <= 2'b00;
		if (ExMemRegWrite && (ExMemRegRd != 5'b0) && (ExMemRegRd == IfIdRegRt))
			ForwardB_EQ <= 2'b10;
		else if (MemWbRegWrite && (MemWbRegRd != 5'b0) && (MemWbRegRd == IfIdRegRt))
			ForwardB_EQ <= 2'b01;
		else
			ForwardB_EQ <= 2'b00;
		end
	end
endmodule

module HazardDetection(IFIDRegRs,IFIDRegRt,IDEXRegDST,IDEXMemRead,IDEXRegWrite,Branch,Stall,clock);
	input [4:0] IFIDRegRs,IFIDRegRt,IDEXRegDST;
	input IDEXMemRead,Branch,IDEXRegWrite,clock;
	output Stall;
	reg Stall,Stall2;

	initial	begin
		Stall <= 0;
		Stall2 <= 0;
	end

	always @ (negedge clock) begin
		Stall <= 0;
		if (Branch)begin
			if (IDEXMemRead && ((IFIDRegRs == IDEXRegDST) || (IFIDRegRt == IDEXRegDST)))begin
				Stall <= 1;
				Stall2 <= 1;
			end 
			else if (IDEXRegWrite && ((IFIDRegRs == IDEXRegDST) || (IFIDRegRt == IDEXRegDST)))begin
				Stall <= 1;
				Stall2 <= 0;
    	    end 
			else if (Stall2)begin
				Stall <= 1;
				Stall2 <= 0;
    		end
		end 
		else 
		if (IDEXMemRead && ((IFIDRegRs == IDEXRegDST) || (IFIDRegRt == IDEXRegDST)))begin
			Stall <= 1;
			Stall2 <= 0;
		end 
		else begin
			Stall <= 0; 
        end
	end
endmodule


module IDEX(clock,rst,RegWrite_in,MemtoReg_in,MemRead_in,MemWrite_in,ALUSrc_in,ALUOp_in,RegDst_in,RegRsData_in,RegRtData_in,Immediate_in,instr_Rs_addr_in,
		instr_Rt_addr_in,instr_Rd_addr_in,RegWrite_out,MemtoReg_out,MemRead_out,MemWrite_out,ALUSrc_out,ALUOp_out,RegDst_out,RegRsData_out,RegRtData_out,
		Immediate_out,instr_Rs_addr_out,instr_Rt_addr_out,instr_Rd_addr_out);
	input clock,rst,RegWrite_in,MemtoReg_in,MemRead_in,MemWrite_in,ALUSrc_in,RegDst_in;
	input [2:0] ALUOp_in;
	input [31:0] RegRsData_in,RegRtData_in,Immediate_in;
	input [4:0] instr_Rs_addr_in,instr_Rt_addr_in,instr_Rd_addr_in;
	output RegWrite_out,MemtoReg_out,MemRead_out,MemWrite_out,ALUSrc_out,RegDst_out;
	output [2:0] ALUOp_out;
	output [31:0] RegRsData_out,RegRtData_out,Immediate_out;
	output [4:0] instr_Rs_addr_out,instr_Rt_addr_out,instr_Rd_addr_out;
	reg RegWrite_out,MemtoReg_out,MemRead_out,MemWrite_out,ALUSrc_out,RegDst_out;
	reg [2:0] ALUOp_out;
	reg	[31:0] RegRsData_out,RegRtData_out,Immediate_out;
	reg	[4:0] instr_Rs_addr_out,instr_Rt_addr_out,instr_Rd_addr_out;

	always @(posedge clock or negedge rst)begin
		if(~rst)begin
			RegWrite_out<=1'b0;
			MemtoReg_out<=1'b0;
			MemRead_out<=1'b0;
			MemWrite_out<=1'b0;
			ALUSrc_out<=1'b0;
			ALUOp_out<=3'b0;
			RegDst_out<=1'b0;
			RegRsData_out<=32'b0;
			RegRtData_out<=32'b0;
			Immediate_out<=32'b0;
			instr_Rs_addr_out<=5'b0;
			instr_Rt_addr_out<=5'b0;
			instr_Rd_addr_out<=5'b0;
		end
		else begin
			RegWrite_out<=RegWrite_in;
			MemtoReg_out<=MemtoReg_in;
			MemRead_out<=MemRead_in;
			MemWrite_out<=MemWrite_in;
			ALUSrc_out<=ALUSrc_in;
			ALUOp_out<=ALUOp_in;
			RegDst_out<=RegDst_in;
			RegRsData_out<=RegRsData_in;
			RegRtData_out<=RegRtData_in;
			Immediate_out<=Immediate_in;
			instr_Rs_addr_out<=instr_Rs_addr_in;
			instr_Rt_addr_out<=instr_Rt_addr_in;
			instr_Rd_addr_out<=instr_Rd_addr_in;
		end
	end
endmodule

module IFID(clock,rst,PC_4_in,instr_in,hazard_in,flush_in,PC_4_out,instr_out);
	input clock,rst,hazard_in,flush_in;
	input [31:0] PC_4_in,instr_in;
	output [31:0] PC_4_out,instr_out;
	reg [31:0] PC_4_out,instr_out;

	always @(posedge clock or negedge rst)begin
		if(~rst)begin
			PC_4_out <=  32'b0;
			instr_out <= 32'b0;
		end
		else begin
			if(~hazard_in)begin
				PC_4_out <= PC_4_out;
				instr_out <= instr_out;
			end
			else begin
				if(flush_in)begin
					PC_4_out <= 32'b0;
					instr_out <= 32'b0;
				end
				else begin
					PC_4_out <= PC_4_in;
					instr_out <= instr_in;
				end
			end
		end
	end
endmodule

module MEMWB(clock,rst,RegWrite_in,MemtoReg_in,MemData_in,ALUData_in,WBregister_in,RegWrite_out,MemtoReg_out,MemData_out,ALUData_out,WBregister_out);
	input clock,rst,RegWrite_in,MemtoReg_in;
	input [31:0] MemData_in,ALUData_in;
	input [4:0] WBregister_in;
	output RegWrite_out,MemtoReg_out;
	output [31:0] MemData_out,ALUData_out;
	output [4:0] WBregister_out;
	reg	RegWrite_out,MemtoReg_out;
	reg	[31:0] MemData_out,ALUData_out;
	reg	[4:0] WBregister_out;

	always @(posedge clock or negedge rst)begin
		if(~rst)begin
			RegWrite_out<=1'b0;
			MemtoReg_out<=1'b0;
			MemData_out<=32'b0;
			ALUData_out<=32'b0;
			WBregister_out<=5'b0;
		end
		else begin
			RegWrite_out<=RegWrite_in;
			MemtoReg_out<=MemtoReg_in;
			MemData_out<=MemData_in;
			ALUData_out<=ALUData_in;
			WBregister_out<=WBregister_in;
		end
	end
endmodule





