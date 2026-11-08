-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen15_affine_singular_hjb_deficit_strictly_negative
-- name    : AvramDividend.Classical.avram_gen15_affine_singular_hjb_deficit_strictly_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:51:28.985336+00:00
-- url     : https://prove2.me/theorems/1610d575-40fb-4d37-9842-da3d7bbeb504
-- title:
--   Strictly negative affine singular HJB deficit for every positive reserve
-- statement:
--   At any strictly positive reserve, the singular negative-jump affine HJB deficit is strictly negative. This provides the exact sign condition for the proposed explicit original-process counterexample and will combine with the source generator formula; the proof is purely real algebra with the positive square-root and inverse-square-root product.
-- source:
--   Real.rpow_add and sq_nonneg at the pinned Mathlib commit.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gen15_affine_singular_hjb_deficit_strictly_negative
    (x : ℝ) (hx : 0 < x) :
    3 - 4 * x ^ (1 / 2 : ℝ) - 2 * x ^ (-(1 / 2 : ℝ)) < 0 := by sorry
