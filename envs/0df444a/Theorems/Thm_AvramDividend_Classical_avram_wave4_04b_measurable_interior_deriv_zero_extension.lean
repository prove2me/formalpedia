-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_interior_deriv_zero_extension
-- name    : AvramDividend.Classical.avram_wave4_04b_measurable_interior_deriv_zero_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:28:26.184156+00:00
-- url     : https://prove2.me/theorems/631bedfa-e1f7-4272-8af2-3c2907741b4a
-- title:
--   Joint-integrand ingredient: measurable zero extension of an interior smooth dividend value derivative
-- statement:
--   If w is C² only on an open interior localisation set s, then the derivative extended by zero outside s is Borel measurable globally. This avoids falsely requiring smoothness or measurability of w outside the cap and supplies the derivative weight for complete Stieltjes dividend control under localised pre-ruin clocks. The result follows from interior derivative continuity and measurable piecewise gluing.
-- source:
--   Pinned Mathlib ContDiffOn.continuousOn_deriv_of_isOpen and ContinuousOn.measurable_piecewise

import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory
open scoped Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_measurable_interior_deriv_zero_extension
    (w : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hw : ContDiffOn ℝ 2 w s) :
    Measurable (fun y : ℝ => if y ∈ s then deriv w y else 0) := by
  sorry
