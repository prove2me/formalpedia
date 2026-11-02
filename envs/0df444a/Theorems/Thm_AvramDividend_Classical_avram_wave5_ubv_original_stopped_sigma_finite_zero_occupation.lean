-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_stopped_sigma_finite_zero_occupation
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_stopped_sigma_finite_zero_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:41:24.634658+00:00
-- url     : https://prove2.me/theorems/398b9dc7-99f7-4a44-aa29-e38471bd5ab1
-- title:
--   Original unbounded-variation controlled reserve has zero lower-boundary occupation before every genuine pre-ruin localiser
-- statement:
--   For the original SpectrallyNegativeLevy X and an actual strategy D adapted to the same filtration, assume unbounded variation and take any extended nonnegative source-path localising clock sigma bounded above by the actual ruinTime. With the explicit dense/cofinal schedules already required by the Proved original zero-occupation theorem, for any sigma-finite time measure the controlled reserve is positive at almost every time earlier than sigma, for almost every original sample path. The theorem removes a separate pre-ruin nonnegative reserve premise by invoking the canonically Proved pathwise riskProcess_nonneg_before_ruin. It applies to every bounded stochastic localiser, without assumptions on w, the cap or the control's Stieltjes structure, and directly provides the zero-boundary drift localisation used by the corrected UBV stochastic core. No Itô-Meyer formula, stochastic martingale budget, or parent theorem is asserted.
-- source:
--   Source-faithful reduction of accepted AvramDividend.Classical.avram_wave4_04_ubv_same_source_positive_preruin_sigma_finite_occupation (6a06830a-160f-45a6-b776-8807e202b19d) via original ruin clock and accepted riskProcess_nonneg_before_ruin (c26c83f7-d703-46b9-a361-bf008b70dfe6). Supports corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706; no core or milestone edit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_positive_preruin_sigma_finite_occupation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_ubv_original_stopped_sigma_finite_zero_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞)
    (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (t : ℝ≥0∞) < σ ω →
        0 < riskProcess X x D t ω := by sorry
