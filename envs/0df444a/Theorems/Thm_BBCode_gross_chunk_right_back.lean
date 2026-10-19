-- Prove2me | Theorems.Thm_BBCode_gross_chunk_right_back
-- name    : BBCode.gross_chunk_right_back
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T09:39:40.323737+00:00
-- url     : https://prove2.me/theorems/e7fc3dda-ae0d-4cab-a39f-fcdc02a20f00
-- title:
--   Gross code: stabilizer subset at the right back anchor branch
-- statement:
--   Consider the gross bivariate-bicycle code of Table 3 on $G=\mathbb Z_{12}\times\mathbb Z_6$, with $A=x^3+y+y^2$, $B=y^3+x+x^2$, and binary check matrices $H_X=[A\mid B]$ and $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$.
--
--   Let $v$ satisfy $H_Xv=0$ and have Hamming weight at most ten. Assume its right block coordinate $(0,0)$ is nonzero and at least one of left block coordinate $(3,3)$, right block coordinate $(1,3)$, right block coordinate $(2,3)$ is nonzero. There is a nonzero Z-stabilizer $u$ supported inside $v$, containing the same anchor coordinate:
--
--   $$H_Xu=0,\qquad u\in\operatorname{row}(H_Z),\qquad u_{\mathrm{anchor}}=1,\qquad\operatorname{supp}(u)\subseteq\operatorname{supp}(v).$$
--
--   This support extraction lemma is one of four anchored cases used to prove the existing gross_small_kernel theorem by removing stabilizer subsets and inducting on support size.
-- source:
--   Bravyi et al., https://arxiv.org/abs/2308.07915v2, Section 4, Lemma 1 and Table 3, row [[144,12,12]]; auxiliary support-extraction case for the distance lower bound.

import Definitions.Def_BBCode_Setting
open Matrix

theorem BBCode.gross_chunk_right_back (v : BBCode.Qubit 12 6 → ZMod 2)
    (hv : BBCode.HX {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inr (0, 0)) ≠ 0)
    (hb : v (Sum.inl (3, 3)) ≠ 0 ∨ v (Sum.inr (1, 3)) ≠ 0 ∨ v (Sum.inr (2, 3)) ≠ 0) :
    ∃ u : BBCode.Qubit 12 6 → ZMod 2,
      BBCode.HX {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)}) ∧
      u (Sum.inr (0, 0)) ≠ 0 ∧ ∀ q, u q ≠ 0 → v q ≠ 0 := by sorry
