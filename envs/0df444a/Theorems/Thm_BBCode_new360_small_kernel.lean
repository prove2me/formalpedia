-- Prove2me | Theorems.Thm_BBCode_new360_small_kernel
-- name    : BBCode.new360_small_kernel
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T15:34:31.207961+00:00
-- url     : https://prove2.me/theorems/ce2ba891-e893-4d37-a15b-2e2f238b2aad
-- title:
--   New 360-qubit code: small kernel vectors are stabilizers
-- statement:
--   Let $G=\mathbb Z_6\times\mathbb Z_{30}$ and let $A=1+y+xy^2$ and $B=1+y^8+x^2y^{16}$. Form the binary circulant check matrices $H_X=[A\mid B]$ and $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$ on the 360 qubits $G\sqcup G$. Every binary vector of weight at most ten with zero X-check syndrome is a Z-stabilizer:
--
--   $$H_Xv=0,\quad |v|\le10\quad\Longrightarrow\quad v\in\operatorname{row}(H_Z).$$
--
--   This is the small-support exclusion used by the reduction of the existing new $[[360,24,12]]$ parameter theorem. The reduction separately proves the check ranks and exhibits weight-twelve nontrivial logical operators. Odd column weights force even kernel weight, so the displayed exclusion supplies the remaining distance lower bound in one sector; group inversion and exchange of the two blocks transfer it to the other sector.
-- source:
--   Auxiliary small-support formulation of the distance lower bound in existing captain milestone BBCode.new360_params, https://prove2.me/theorems/5cfa9063-07f8-4665-9813-ea43082ce94a. Its cited reference is Daugherty, Ryan and Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits (2026), Table 3 p.5 and polynomials Table 9 p.15. General BB distance and sector-duality formulation: Bravyi et al., arXiv:2308.07915v2, Section 4, Lemma 1; https://arxiv.org/html/2308.07915v2#S4.

import Definitions.Def_BBCode_Setting
open Matrix

theorem BBCode.new360_small_kernel (v : BBCode.Qubit 6 30 → ZMod 2)
    (hv : BBCode.HX (l := 6) (m := 30) {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10) :
    v ∈ BBCode.rowSpace (BBCode.HZ (l := 6) (m := 30)
      {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)}) := by sorry
