-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_true_clock_signed_HJB_expected_nonpos
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_true_clock_signed_HJB_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:21:29.719056+00:00
-- url     : https://prove2.me/theorems/773f3823-02be-409e-ae27-6857254a3557
-- title:
--   True physical clock expected signed BV HJB source jump residual is nonpositive
-- statement:
--   At the actual original physical mapped-Lebesgue finite horizon clock times the original probability P, the predictable interior-localised compensated BV generator residual has a nonpositive integral. The original controlled pre-source state is tied explicitly to x+X-rightLimit D by hUpre and the actual X.drift and X.ν are used. The time-path signed integrand F is required to be genuinely Integrable, preventing an unsupported optional stopping or Fubini step. This is an unconditional P2-independent expected HJB term, to be paired with the separate original stochastic P2 jump-compensation bridge.
-- source:
--   Proved original generator and discounted HJB sign plus Mathlib integral_nonpos_of_ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_discounted_HJB_source_jump_residual_nonpos
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_true_clock_signed_HJB_expected_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (x : ℝ) (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0) (Upre : ℝ≥0 × Ω → ℝ) (hUpre : ∀ p, Upre p = Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) (E : Set (ℝ≥0 × Ω)) (hEpred : MeasurableSet[𝓕.rightCont.predictable] E) (hGen : ∀ p ∈ E, X.GeneratorIntegrable w (Upre p)) (hHJB : ∀ p ∈ E, X.generator w (Upre p) - q * w (Upre p) ≤ 0) (F : ℝ≥0 × Ω → ℝ) (hF : ∀ p, F p = if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * (X.drift * deriv w (Upre p) + (∫ z in Iio (0 : ℝ), w (Upre p + z) - w (Upre p) ∂X.ν) - q * w (Upre p)) else 0) (hFint : Integrable F ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) : (∫ p, F p ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) ≤ 0 := by sorry
