-- Prove2me | Theorems.Thm_BBCode_bb108_left_back
-- name    : BBCode.bb108_left_back
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T07:55:02.51777+00:00
-- url     : https://prove2.me/theorems/ad0c00d8-5391-4a81-aa41-d035ec61a81c
-- title:
--   BB108 short kernel support at the left back anchor branch
-- statement:
--   Consider the bivariate-bicycle code of Table 3 on $G=\mathbb Z_9\times\mathbb Z_6$, with $A=x^3+y+y^2$ and $B=y^3+x+x^2$. Its check matrices are $H_X=[A\mid B]$ and $H_Z=[B^T\mid A^T]$, where each polynomial acts by its circulant on $G$.
--
--   Let $v$ be a binary vector on the two qubit blocks with $H_Xv=0$ and Hamming weight at most eight. Assume its left block coordinate $(0,0)$ is nonzero and at least one of right block coordinate $(0,1)$, right block coordinate $(1,4)$, right block coordinate $(2,4)$ is nonzero. Then
--
--   $$v\in\operatorname{row}(H_Z).$$
--
--   This anchored support lemma is one of four cases used to establish the distance lower bound in the existing BBCode.bb108_params milestone.
-- source:
--   Bravyi et al., https://arxiv.org/abs/2308.07915v2, Section 4, Lemma 1 and Table 3, row [[108,8,10]]; auxiliary anchored case of the distance lower bound.

import Definitions.Def_BBCode_Setting
open Matrix

theorem BBCode.bb108_left_back (v : BBCode.Qubit 9 6 → ZMod 2)
    (hv : BBCode.HX {(3, 0), (0, 1), (0, 2)} {(0, 3), (1, 0), (2, 0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 8)
    (ha : v (Sum.inl (0, 0)) ≠ 0)
    (hb : v (Sum.inr (0, 1)) ≠ 0 ∨ v (Sum.inr (1, 4)) ≠ 0 ∨ v (Sum.inr (2, 4)) ≠ 0) :
    v ∈ BBCode.rowSpace (BBCode.HZ {(3, 0), (0, 1), (0, 2)} {(0, 3), (1, 0), (2, 0)}) := by sorry
