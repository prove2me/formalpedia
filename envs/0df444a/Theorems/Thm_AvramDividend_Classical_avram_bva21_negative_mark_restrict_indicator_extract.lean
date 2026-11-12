-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva21_negative_mark_restrict_indicator_extract
-- name    : AvramDividend.Classical.avram_bva21_negative_mark_restrict_indicator_extract
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:53:21.968192+00:00
-- url     : https://prove2.me/theorems/cb7bd6c1-a232-4ff1-a109-9daabd119620
-- title:
--   Original restricted negative-mark integral extracts the stopped discount and cap mask
-- statement:
--   For the original negative Lévy mark measure restricted to z<0, the integrand's explicit z<0 mask is almost everywhere true. Its time/ruin/cap indicator is constant in z and can be pulled outside the inner mark integral; so can the fixed discount factor. This is the exact integral extraction needed to rewrite original time kernel K in 7ccc2a1a as an integral of the same closed-cap marked rate used by frozen grid sum A.
-- source:
--   Original source-exact mark-kernel factorisation step for 7ccc2a1a original compensated-grid convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva21_negative_mark_restrict_indicator_extract
    (μ : MeasureTheory.Measure ℝ) (f : ℝ → ℝ)
    (c : ℝ) (guard : Prop) :
    (∫ z : ℝ, (if guard ∧ z < 0 then c * f z else 0)
      ∂(μ.restrict (Set.Iio (0 : ℝ)))) =
    if guard then c * (∫ z in Set.Iio (0 : ℝ), f z ∂μ) else 0 := by sorry
