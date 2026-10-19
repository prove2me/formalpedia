-- Prove2me | Theorems.Thm_BBCode_bb90_left_back
-- name    : BBCode.bb90_left_back
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T07:09:53.265851+00:00
-- url     : https://prove2.me/theorems/fbc85b25-a722-42a9-92ff-e301706388da
-- title:
--   BB90 short kernel support at the left back anchor branch
-- statement:
--   For the Table 3 code on $G=\mathbb Z_{15}\times\mathbb Z_3$, with $A=x^9+y+y^2$ and $B=1+x^2+x^7$, let $v$ lie in $\ker H_X$ and have Hamming weight at most eight. Suppose its left block coordinate $(0,0)$ is nonzero, and at least one of right block coordinate $(0,1)$, right block coordinate $(2,1)$, right block coordinate $(7,1)$ is nonzero. Then $v$ belongs to the row space of $H_Z$, so it is a stabilizer. This anchored support lemma is a finite-search case used in the reduction of the existing BBCode.bb90_params distance lower bound; it does not assert a new code construction.
-- source:
--   Bravyi et al., arXiv:2308.07915v2, Section 4, Lemma 1 and Table 3, row [[90,8,10]]; auxiliary anchored case of the distance lower bound.

import Definitions.Def_BBCode_Setting
open Matrix

theorem BBCode.bb90_left_back (v : BBCode.Qubit 15 3 → ZMod 2)
    (hv : BBCode.HX {(9, 0), (0, 1), (0, 2)} {(0, 0), (2, 0), (7, 0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 8)
    (ha : v (Sum.inl (0, 0)) ≠ 0)
    (hb : v (Sum.inr (0, 1)) ≠ 0 ∨ v (Sum.inr (2, 1)) ≠ 0 ∨ v (Sum.inr (7, 1)) ≠ 0) :
    v ∈ BBCode.rowSpace (BBCode.HZ {(9, 0), (0, 1), (0, 2)} {(0, 0), (2, 0), (7, 0)}) := by sorry
