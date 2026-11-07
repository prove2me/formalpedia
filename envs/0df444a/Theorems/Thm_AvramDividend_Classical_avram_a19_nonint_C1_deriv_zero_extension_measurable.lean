-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_C1_deriv_zero_extension_measurable
-- name    : AvramDividend.Classical.avram_a19_nonint_C1_deriv_zero_extension_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:50:40.800964+00:00
-- url     : https://prove2.me/theorems/915d1b87-91d2-4a16-ad8d-50dd123a233d
-- title:
--   C1 interior derivative has a measurable zero extension
-- statement:
--   On any open real set, the derivative of a C1 function is continuous, hence its extension by zero outside that set is measurable.
-- source:
--   First-order strengthening of the Proved C2 result 631bedfa. Genuine Borel derivative factor required by the actual BV A19 stopped raw-jump residual grid-measurability.

import Mathlib
open Classical MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_a19_nonint_C1_deriv_zero_extension_measurable
    (w : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hw : ContDiffOn ℝ 1 w s) :
    Measurable (fun y : ℝ => if y ∈ s then deriv w y else 0) := by sorry
