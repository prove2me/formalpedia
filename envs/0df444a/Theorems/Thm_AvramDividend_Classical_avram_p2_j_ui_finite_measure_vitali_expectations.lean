-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_vitali_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_finite_measure_vitali_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:03:22.190142+00:00
-- url     : https://prove2.me/theorems/b1b85a32-70cd-4eeb-aaf0-f620dfaeeea7
-- title:
--   Vitali a.e. convergence of Bochner means for finite measures without probability normalisation
-- statement:
--   Let mu be a finite measure, not necessarily a probability measure, and Y_n measurable real functions uniformly integrable in L1(mu). If Y_n converges mu-almost everywhere to Z, prove Z is Bochner integrable and real integrals converge. Finite total mass is the exact hypothesis of pinned Mathlib tendsto_Lp_finite_of_tendsto_ae; it rules out escape of integrable mass at infinity.

import Mathlib

open MeasureTheory Filter

/-! Genuine Bochner mean convergence under uniform integrability on finite measures. -/

theorem AvramDividend.Classical.avram_p2_j_ui_finite_measure_vitali_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hUI : UniformIntegrable Y 1 μ)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)) := by sorry
