open util/ordering[I] as Iord																-- ordering constraints for rows
open util/ordering[J] as Jord																-- ordering constraints for colums
abstract sig I {}
one sig i1,i2,i3,i4,i5,i6,i7,i8,i9 extends I {}												-- ints are not constrained enough
fact { 																						-- well order the 9 explicit rows
	Iord/first=i1
	Iord/next[i1]=i2
	Iord/next[i2]=i3
	Iord/next[i3]=i4
	Iord/next[i4]=i5
	Iord/next[i5]=i6
	Iord/next[i6]=i7
	Iord/next[i7]=i8
	Iord/next[i8]=i9
}
abstract sig J {}
one sig j1,j2,j3,j4,j5,j6,j7,j8,j9 extends J {}												-- ints not constrained enough
fact { 																					 	-- well order the 9 explicit columns
	Jord/first=j1
	Jord/next[j1]=j2
	Jord/next[j2]=j3
	Jord/next[j3]=j4
	Jord/next[j4]=j5
	Jord/next[j5]=j6
	Jord/next[j6]=j7
	Jord/next[j7]=j8
	Jord/next[j8]=j9
}
one sig Board {
    cell: I -> J -> one Int,
} { 
	all i:I,j:J | cell[i][j]>=1 and cell[i][j]<=9 											-- all cell values 1 through 9
    no i:I | some disj a,b:J | cell[i][a]=cell[i][b]                                        -- unique rows
    no j:J | some disj a,b:I | cell[a][j]=cell[b][j]                                        -- unique cols
    no i:i1+i2+i3,j:j1+j2+j3 | some oi:i1+i2+i3-i,oj:j1+j2+j3-j | cell[i][j]=cell[oi][oj]   -- unique block1
    no i:i4+i5+i6,j:j1+j2+j3 | some oi:i4+i5+i6-i,oj:j1+j2+j3-j | cell[i][j]=cell[oi][oj]	-- unique block2
    no i:i7+i8+i9,j:j1+j2+j3 | some oi:i7+i8+i9-i,oj:j1+j2+j3-j | cell[i][j]=cell[oi][oj]   -- unique block3
    no i:i1+i2+i3,j:j4+j5+j6 | some oi:i1+i2+i3-i,oj:j4+j5+j6-j | cell[i][j]=cell[oi][oj]   -- unique block4
    no i:i4+i5+i6,j:j4+j5+j6 | some oi:i4+i5+i6-i,oj:j4+j5+j6-j | cell[i][j]=cell[oi][oj]   -- unique block5
    no i:i7+i8+i9,j:j4+j5+j6 | some oi:i7+i8+i9-i,oj:j4+j5+j6-j | cell[i][j]=cell[oi][oj]   -- unique block6
    no i:i1+i2+i3,j:j7+j8+j9 | some oi:i1+i2+i3-i,oj:j7+j8+j9-j | cell[i][j]=cell[oi][oj]   -- unique block7
    no i:i4+i5+i6,j:j7+j8+j9 | some oi:i4+i5+i6-i,oj:j7+j8+j9-j | cell[i][j]=cell[oi][oj]   -- unique block8
    no i:i7+i8+i9,j:j7+j8+j9 | some oi:i7+i8+i9-i,oj:j7+j8+j9-j | cell[i][j]=cell[oi][oj]   -- unique block9
}
abstract sig RowHint {
	row: one I,  																			-- hints row
	h1: one J, h2: one J, h3: one J, h4: one J, h5: one J, h6: one J,  						-- 6 hint column indicies
	v1: one Int, v2: one Int, v3: one Int, v4: one Int, v5: one Int,  						-- 5 hint values between
} {
	h1=j1 and h6=j9 																		-- hints span the whole row
	lte[h1,h2] and lte[h2,h3] and lte[h3,h4] and lte[h4,h5] and lte[h5,h6] 					-- hints are well ordered
	(v1=sum[Board.cell[row][{j:J | gte[j,h1] and lt[j,h2]}]]) or (h1=h2 and v1=0) 			-- hint1
	(v2=sum[Board.cell[row][{j:J | gte[j,h2] and lt[j,h3]}]]) or (h2=h3 and v2=0) 			-- hint2
	(v3=sum[Board.cell[row][{j:J | gte[j,h3] and lt[j,h4]}]]) or (h3=h4 and v3=0) 			-- hint3
	(v4=sum[Board.cell[row][{j:J | gte[j,h4] and lt[j,h5]}]]) or (h4=h5 and v4=0) 			-- hint4
	(v5=sum[Board.cell[row][{j:J | gte[j,h5] and lte[j,h6]}]]) 								-- hint5 (never null)
	v1>=0 and v2>=0 and v3>=0 and v4>=0 and v5>=0											-- hints are positive (Integer space doesnt overflow)
	v1=0 or v2=0 or v3=0 or v4=0															-- at least one hint is null
}
one sig r1 extends RowHint {} {row=i1}														-- fix the row hint space
one sig r2 extends RowHint {} {row=i2}
one sig r3 extends RowHint {} {row=i3}
one sig r4 extends RowHint {} {row=i4}
one sig r5 extends RowHint {} {row=i5}
one sig r6 extends RowHint {} {row=i6}
one sig r7 extends RowHint {} {row=i7}
one sig r8 extends RowHint {} {row=i8}
one sig r9 extends RowHint {} {row=i9}
abstract sig ColHint {
	col: one J,																				-- hints column
	h1: one I, h2: one I, h3: one I, h4: one I, h5: one I, h6: one I,						-- 6 hint row indicies
	v1: one Int, v2: one Int, v3: one Int, v4: one Int, v5: one Int, 						-- 5 hints between
} {
	h1=i1 and h6=i9 																		-- hints span the whole row
	lte[h1,h2] and lte[h2,h3] and lte[h3,h4] and lte[h4,h5] and lte[h5,h6]					-- hints are well ordered
	(v1=sum[Board.cell[{i:I | gte[i,h1] and lt[i,h2]}][col]]) or (h1=h2 and v1=0)			-- hint1
	(v2=sum[Board.cell[{i:I | gte[i,h2] and lt[i,h3]}][col]]) or (h2=h3 and v2=0)			-- hint2
	(v3=sum[Board.cell[{i:I | gte[i,h3] and lt[i,h4]}][col]]) or (h3=h4 and v3=0)			-- hint3
	(v4=sum[Board.cell[{i:I | gte[i,h4] and lt[i,h5]}][col]]) or (h4=h5 and v4=0)			-- hint4
	(v5=sum[Board.cell[{i:I | gte[i,h5] and lte[i,h6]}][col]])								-- hint5 (never null)
	v1>=0 and v2>=0 and v3>=0 and v4>=0 and v5>=0											-- hints are positive (Integer space doesnt overflow)
	v1=0 or v2=0 or v3=0 or v4=0															-- at least one hint is null
}
one sig c1 extends ColHint {} {col=j1}														-- fix the column hint space
one sig c2 extends ColHint {} {col=j2}
one sig c3 extends ColHint {} {col=j3}
one sig c4 extends ColHint {} {col=j4}
one sig c5 extends ColHint {} {col=j5}
one sig c6 extends ColHint {} {col=j6}
one sig c7 extends ColHint {} {col=j7}
one sig c8 extends ColHint {} {col=j8}
one sig c9 extends ColHint {} {col=j9}
pred daily {
	r1.v5=9 	and r1.v4=36 	and r1.v3=0 	and r1.v2=0 	and r1.v1=0
	r2.v5=6 	and r2.v4=28 	and r2.v3=11 	and r2.v2=0 	and r2.v1=0
	r3.v5=24 	and r3.v4=9 	and r3.v3=5 	and r3.v2=7 	and r3.v1=0
	r4.v5=15 	and r4.v4=14 	and r4.v3=12 	and r4.v2=4 	and r4.v1=0
	r5.v5=6 	and r5.v4=35 	and r5.v3=4 	and r5.v2=0 	and r5.v1=0
	r6.v5=45 	and r6.v4=0 	and r6.v3=0 	and r6.v2=0 	and r6.v1=0
	r7.v5=18 	and r7.v4=27 	and r7.v3=0 	and r7.v2=0 	and r7.v1=0
	r8.v5=11 	and r8.v4=2 	and r8.v3=12 	and r8.v2=20 	and r8.v1=0
	r9.v5=4 	and r9.v4=3 	and r9.v3=38 	and r9.v2=0 	and r9.v1=0
	c1.v5=6 	and c1.v4=34 	and c1.v3=5 	and c1.v2=0 	and c1.v1=0
	c2.v5=16 	and c2.v4=6 	and c2.v3=5 	and c2.v2=18 	and c2.v1=0
	c3.v5=30 	and c3.v4=15 	and c3.v3=0 	and c3.v2=0 	and c3.v1=0
	c4.v5=10 	and c4.v4=14 	and c4.v3=21 	and c4.v2=0 	and c4.v1=0
	c5.v5=20 	and c5.v4=25 	and c5.v3=0 	and c5.v2=0 	and c5.v1=0
	c6.v5=14 	and c6.v4=31 	and c6.v3=0 	and c6.v2=0 	and c6.v1=0
	c7.v5=18 	and c7.v4=5 	and c7.v3=22 	and c7.v2=0 	and c7.v1=0
	c8.v5=3 	and c8.v4=42 	and c8.v3=0 	and c8.v2=0 	and c8.v1=0
	c9.v5=9 	and c9.v4=11 	and c9.v3=25 	and c9.v2=0 	and c9.v1=0
}
run {} for 9 I, 9 J, 9 RowHint, 9 ColHint, 7 Int											-- will generate a random board
run daily for 9 I, 9 J, 9 RowHint, 9 ColHint, 7 Int											-- add predicates for hint values to solve a given board
