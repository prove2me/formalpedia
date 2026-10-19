-- Prove2me | Theorems.Thm_BBCode_gross_small_kernel
-- name    : BBCode.gross_small_kernel
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T08:36:33.831168+00:00
-- url     : https://prove2.me/theorems/3d44c28f-7905-46fd-a962-94a000fa6f7c
-- title:
--   Gross code: every kernel vector of weight at most ten is a stabilizer
-- statement:
--   Let $G=\mathbb Z_{12}\times\mathbb Z_6$ and let $A=x^3+y+y^2$ and $B=y^3+x+x^2$. Write $H_X=[A\mid B]$ and $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$ for the binary circulant check matrices of the gross code.
--
--   Every binary vector on its 144 qubits that has zero X-check syndrome and Hamming weight at most ten is a Z-stabilizer:
--   $$H_Xv=0,\quad |v|\le10\quad\Longrightarrow\quad v\in\operatorname{row}(H_Z).$$
--
--   This is the remaining small-support exclusion needed in the reduction of the existing gross-code parameter theorem. The parent reduction independently certifies both check ranks and weight-twelve nontrivial logical operators. Each X-check column has odd weight, so any kernel vector has even weight; this exclusion therefore gives the Z-distance lower bound twelve. Group inversion and exchange of the two qubit blocks give the same lower bound in the X sector.
-- source:
--   Bravyi et al., High-threshold and low-overhead fault-tolerant quantum memory, arXiv:2308.07915v2, Section 4, Lemma 1 and Table 3 ([[144,12,12]] row); https://arxiv.org/html/2308.07915v2#S4 . Small-support formulation of its distance lower bound, for the reduction of BBCode.gross_params.

import Definitions.Def_BBCode_Setting
open Matrix

theorem BBCode.gross_small_kernel (v : BBCode.Qubit 12 6 → ZMod 2)
    (hv : BBCode.HX (l := 12) (m := 6) {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10) :
    v ∈ BBCode.rowSpace (BBCode.HZ (l := 12) (m := 6)
      {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)}) := by sorry
