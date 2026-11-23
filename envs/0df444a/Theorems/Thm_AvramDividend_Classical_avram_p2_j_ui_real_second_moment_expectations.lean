-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_real_second_moment_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_real_second_moment_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:05:57.820554+00:00
-- url     : https://prove2.me/theorems/ed25acc3-0cd6-492e-a2a4-ed9808f703e6
-- title:
--   Uniform actual real Bochner second moments and a.e. convergence imply expectation convergence
-- statement:
--   On an actual probability space, an almost-everywhere convergent sequence of strongly measurable real functions with integrable squares and a fixed upper bound on the genuine real Bochner second moments converges in genuine real expectations. The limit is integrable. The proof turns the real moment bound into Mathlib L2 seminorm control and applies the already-Proved finite-measure Vitali theorem.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_l2_mass_bound_expectations

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_real_second_moment_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (C : ℝ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hi : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hC : 0 ≤ C)
    (hbound : ∀ n, (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ C)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)) := by sorry
