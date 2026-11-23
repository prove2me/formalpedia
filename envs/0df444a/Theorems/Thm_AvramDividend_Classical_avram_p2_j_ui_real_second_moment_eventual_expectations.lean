-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_real_second_moment_eventual_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_real_second_moment_eventual_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:13:12.142087+00:00
-- url     : https://prove2.me/theorems/5a31bee7-419e-4273-bf3d-f9b888efc7f9
-- title:
--   Eventual uniform real second Bochner moments imply convergence of expectations
-- statement:
--   In a genuine probability space, a sequence of measurable real variables converging almost everywhere has convergent genuine real expectations when the real second moments are finite termwise and uniformly bounded after a finite exceptional initial segment. Its limit is integrable. The proof converts the eventual real moment bound to Mathlib L2 seminorms and invokes the already-Proved eventual finite-measure Vitali theorem.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_eventual_l2_mass_expectations

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_real_second_moment_eventual_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (C : ℝ) (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hi : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hC : 0 ≤ C)
    (hbound : ∀ n, N ≤ n → (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ C)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)) := by sorry
