-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_zero_mass_bounded_lintegral_vanishes
-- name    : AvramDividend.Classical.avram_p2_b_rate_zero_mass_bounded_lintegral_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:40:36.223128+00:00
-- url     : https://prove2.me/theorems/d3fe9344-a5de-4f1b-a275-5c7ca0a1dacd
-- title:
--   Vanishing masses force convergence of all uniformly bounded nonnegative tests
-- statement:
--   A family of measures with total masses tending to zero as h approaches zero from above has integrals of every fixed nonnegative measurable or outer-integrable test g bounded by a finite constant C also tending to zero. This independently closes the zero-limiting-mass branch of the proposed weighted exponential-image finite-measure method of moments, without illicit normalisation by zero.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_zero_mass_bounded_lintegral_vanishes
    (μ : ℝ → Measure ℝ) (g : ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : C ≠ ⊤) (hgbound : ∀ z : ℝ, g z ≤ C)
    (hmass : Tendsto (fun h : ℝ => μ h Set.univ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ≥0∞))) :
    Tendsto (fun h : ℝ => ∫⁻ z : ℝ, g z ∂(μ h))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ≥0∞)) := by sorry
