-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_eventual_nonnegative_lintegral_convergence
-- name    : AvramDividend.Classical.avram_p2_j_ui_finite_eventual_nonnegative_lintegral_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:22:37.66189+00:00
-- url     : https://prove2.me/theorems/6d3dbf49-3be4-4fbb-9dac-b8e3786bb6b2
-- title:
--   Finite-measure eventual L2 control yields convergence of actual nonnegative ENNReal expectations
-- statement:
--   On a finite measure not necessarily normalised to probability, let nonnegative measurable Y_n converge almost everywhere to Z and satisfy a uniform L2 bound only after a finite index N. A finite NNReal total-mass bound R suffices to prove Z is integrable and nonnegative a.e. and that the full original sequence of genuine ENNReal lintegrals converges to the lintegral of Z. The first N terms need not be integrable.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_eventual_l2_mass_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_nonnegative_real_to_ennreal_mean_convergence

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! Finite-measure eventual L2 control transfers a.e limits to genuine ENNReal means. -/

theorem AvramDividend.Classical.avram_p2_j_ui_finite_eventual_nonnegative_lintegral_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (B R : ℝ≥0) (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hB : ∀ n, N ≤ n → eLpNorm (Y n) 2 μ ≤ (B : ENNReal))
    (hMass : (μ Set.univ) ^ (1 / 2 : ℝ) ≤ (R : ENNReal))
    (hNonneg : ∀ n ω, 0 ≤ Y n ω)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧ (0 ≤ᵐ[μ] Z) ∧
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂μ)
        atTop (nhds (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)) := by sorry
