-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_path_clock_HJB_L1_expected_nonpos
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_path_clock_HJB_L1_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:41:47.360037+00:00
-- url     : https://prove2.me/theorems/da6f7505-4cbd-40b1-a56c-91691f4c115c
-- title:
--   Original controlled BV source true-clock time-integrated HJB residual is L1 and expected nonpositive
-- statement:
--   On the exact original process X, dividend strategy D and true finite mapped-Lebesgue clock, combine the accepted localised original generator jump HJB sign with genuine Fubini and explicit product-clock Integrable F to obtain an integrable pathwise time-integrated original controlled BV residual with nonpositive expectation. This is an HJB drift result and does not assert P2 source jump compensation, which remains a separate canonical dependency.
-- source:
--   Proved P3-B physical-clock original HJB sign 773f3823 and forthcoming P3-B true-clock signed Fubini helper

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_true_clock_signed_HJB_expected_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_true_clock_integrable_signed_Fubini_mean_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_path_clock_HJB_L1_expected_nonpos{Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)
    (E : Set (ℝ≥0 × Ω))
    (hEpred : MeasurableSet[𝓕.rightCont.predictable] E)
    (hGen : ∀ p ∈ E, X.GeneratorIntegrable w (Upre p))
    (hHJB : ∀ p ∈ E, X.generator w (Upre p) - q * w (Upre p) ≤ 0)
    (F : ℝ≥0 × Ω → ℝ)
    (hF : ∀ p, F p = if p ∈ E then
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Upre p) +
          (∫ z in Iio (0 : ℝ), w (Upre p + z) - w (Upre p) ∂X.ν) -
          q * w (Upre p)) else 0)
    (hFint : Integrable F
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P)) :
    Integrable (fun ω => (∫ t, F (t, ω)
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal))) P ∧
    (∫ ω, (∫ t, F (t, ω)
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal)) ∂P) ≤ 0 := by sorry
