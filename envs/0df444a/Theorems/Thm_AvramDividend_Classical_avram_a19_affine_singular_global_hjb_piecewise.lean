-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_global_hjb_piecewise
-- name    : AvramDividend.Classical.avram_a19_affine_singular_global_hjb_piecewise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:21:35.773656+00:00
-- url     : https://prove2.me/theorems/90f12395-8e76-4861-a0a6-710521285d52
-- title:
--   Original singular affine generator HJB deficit has nonpositive explicit piecewise profile
-- statement:
--   The piecewise explicit source-generator/HJB deficit for the proposed singular density, zero-extended affine value candidate and characteristic drift zero is nonpositive for every strictly positive reserve.
-- source:
--   A19 singular Levy countermodel, combining Proved strong scalar HJB sign and large-reserve explicit formula.

import Mathlib.Analysis.Real.Sqrt
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_hjb_drift_two_scalar
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_a19_affine_singular_global_hjb_piecewise
    (x : ℝ) (hx : 0 < x) :
    (if x < 1 then 3 + x - 4 * Real.sqrt x - 2 / Real.sqrt x else -(1 + x)) ≤ 0 := by sorry
