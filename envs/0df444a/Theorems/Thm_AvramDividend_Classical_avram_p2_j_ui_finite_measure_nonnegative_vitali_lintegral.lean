-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_nonnegative_vitali_lintegral
-- name    : AvramDividend.Classical.avram_p2_j_ui_finite_measure_nonnegative_vitali_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:17:16.324778+00:00
-- url     : https://prove2.me/theorems/2e851383-0f19-4c95-b957-8066fba120d8
-- title:
--   Finite-measure nonnegative uniformly integrable a.e. grids converge in genuine ENNReal mass
-- statement:
--   For any finite measure mu, with no probability normalisation required, a uniformly integrable sequence of pointwise nonnegative real grids converging almost everywhere to Z has an integrable nonnegative limit, and genuine ENNReal lintegral expectations converge. Combine the pinned finite-measure Bochner Vitali theorem and the independently proved nonnegative Bochner-to-ENNReal identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_vitali_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_nonnegative_real_to_ennreal_mean_convergence

open MeasureTheory Filter AvramDividend.Classical
open scoped ENNReal

/-! Finite-measure nonnegative Vitali limits converge in genuine ENNReal means. -/

theorem AvramDividend.Classical.avram_p2_j_ui_finite_measure_nonnegative_vitali_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hUI : UniformIntegrable Y 1 μ)
    (hNonneg : ∀ n ω, 0 ≤ Y n ω)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧ (0 ≤ᵐ[μ] Z) ∧
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂μ)
        atTop (nhds (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)) := by sorry
