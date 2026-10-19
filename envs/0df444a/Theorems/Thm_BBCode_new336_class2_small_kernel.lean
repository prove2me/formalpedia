-- Prove2me | Theorems.Thm_BBCode_new336_class2_small_kernel
-- name    : BBCode.new336_class2_small_kernel
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T14:41:56.093065+00:00
-- url     : https://prove2.me/theorems/80e5919a-85e4-4a61-baff-72669c697da6
-- title:
--   New 336-qubit code, class 2: small kernel vectors are stabilizers
-- statement:
--   Let $G=\mathbb Z_2\times\mathbb Z_{84}$ and let $A=1+y+xy^5$ and $B=1+y^{20}+y^{46}$. Form the binary circulant check matrices $H_X=[A\mid B]$ and $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$ on the 336 qubits $G\sqcup G$. Every binary vector of weight at most ten with zero X-check syndrome is a Z-stabilizer:
--
--   $$H_Xv=0,\quad |v|\le10\quad\Longrightarrow\quad v\in\operatorname{row}(H_Z).$$
--
--   This is the small-support exclusion used by the reduction of the existing class-2 $[[336,20,12]]$ parameter theorem. The reduction separately proves the check ranks and exhibits weight-twelve nontrivial logical operators. Odd column weights force even kernel weight, so the displayed exclusion supplies the remaining distance lower bound in one sector; group inversion and exchange of the two blocks transfer it to the other sector.
-- source:
--   Auxiliary small-support formulation of the distance lower bound in existing captain milestone BBCode.new336_class2_params, https://prove2.me/theorems/c1c39db9-186d-4fcc-8fd4-0507b8f1f0d0. Its cited reference is Daugherty, Ryan and Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits (2026), Table 3 p.5 and polynomials Table 9 p.15. General BB distance and sector-duality formulation: Bravyi et al., arXiv:2308.07915v2, Section 4, Lemma 1; https://arxiv.org/html/2308.07915v2#S4.

import Definitions.Def_BBCode_Setting
open Matrix

theorem BBCode.new336_class2_small_kernel (v : BBCode.Qubit 2 84 → ZMod 2)
    (hv : BBCode.HX (l := 2) (m := 84) {(0,0),(0,1),(1,5)} {(0,0),(0,20),(0,46)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10) :
    v ∈ BBCode.rowSpace (BBCode.HZ (l := 2) (m := 84)
      {(0,0),(0,1),(1,5)} {(0,0),(0,20),(0,46)}) := by sorry
