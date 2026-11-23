-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_l2_l1_bound_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_finite_measure_l2_l1_bound_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:03:28.016747+00:00
-- url     : https://prove2.me/theorems/e77a2300-2a60-4fbf-b9c5-747e48aa0a05
-- title:
--   Finite-measure uniform L2 and L1 norm bounds imply a.e.-to-Bochner expectation convergence
-- statement:
--   On any finite measure space, let measurable real Y_n have a uniform L2 norm bound B and a uniform L1 norm bound D. Under almost-everywhere convergence to Z, prove Z is Bochner integrable and the integrals of Y_n converge. A quantitative restricted Cauchy-Schwarz bound implies uniform integrability. Unlike earlier P2-J helpers, the measure need not have total mass one.

import Mathlib

open MeasureTheory Filter
open scoped NNReal ENNReal

/-! On finite measures, bounded L2 and L1 norms give Vitali mean convergence. -/

theorem AvramDividend.Classical.avram_p2_j_ui_finite_measure_l2_l1_bound_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (B D : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (h2 : ∀ n, eLpNorm (Y n) 2 μ ≤ (B : ENNReal))
    (h1 : ∀ n, eLpNorm (Y n) 1 μ ≤ (D : ENNReal))
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)) := by sorry
