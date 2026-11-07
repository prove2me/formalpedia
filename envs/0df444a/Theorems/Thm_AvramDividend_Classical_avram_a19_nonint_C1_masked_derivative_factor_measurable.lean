-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_C1_masked_derivative_factor_measurable
-- name    : AvramDividend.Classical.avram_a19_nonint_C1_masked_derivative_factor_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:53:52.898172+00:00
-- url     : https://prove2.me/theorems/0d1a53bc-f7e9-41ac-a1b2-ad694cc1fa30
-- title:
--   Original stopped-cell C1 gradient factor is measurable on a masked interior event
-- statement:
--   Given a measurable pre-dividend reserve, a measurable active event contained in the C1 smooth interior and a constant discount factor, the original masked derivative coefficient is measurable.
-- source:
--   Generic but mathematically genuine analytic coefficient leaf for the raw-jump residual weighted original BV physical grid. Uses the exact first-order measurable derivative extension.

import Mathlib
open Classical MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a19_nonint_C1_masked_derivative_factor_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (w : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hw : ContDiffOn ℝ 1 w s) (Z : Ω → ℝ) (hZ : Measurable Z)
    (E : Set Ω) (hE : MeasurableSet E)
    (hEi : ∀ ω ∈ E, Z ω ∈ s) (a : ℝ) :
    Measurable (fun ω => if ω ∈ E then a * deriv w (Z ω) else 0) := by sorry
