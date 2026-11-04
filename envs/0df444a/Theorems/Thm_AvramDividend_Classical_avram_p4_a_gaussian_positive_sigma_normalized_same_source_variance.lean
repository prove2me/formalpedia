-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_positive_sigma_normalized_same_source_variance
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_normalized_same_source_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:49:14.636279+00:00
-- url     : https://prove2.me/theorems/5c45a634-f716-4119-b401-02951cc0020e
-- title:
--   Positive Gaussian branch gives unit variance after normalising the same-source continuous residual
-- statement:
--   Given the exact original-path Lévy–Itô extraction with jump-bearing source X, a ν=0 same-Ω same-filtration Gaussian source Y matching the original coefficient, and σ>0, the residual X_t−t c−Jsmall_t−Jlarge_t divided by X.σ has second moment t. This identifies the correct Brownian normalisation for a possible future same-source stochastic integral without claiming that a Brownian path decomposition has been constructed or that quadratic variation follows from one-time variance.
-- source:
--   Authoritative original Lévy decomposition hypothesis and previously Proved same-source stopped zero-jump Gaussian exact variance 3c7623a6-ce31-4f8a-adc6-d73b0ebd8747; generator convention σ²/2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_normalized_same_source_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (ω : Ω),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : 0 < X.σ) (t : ℝ≥0) :
    (∫ ω, ((X.X t ω - (t : ℝ) * X.c -
      Jsmall t ω - Jlarge t ω) / X.σ) ^ 2 ∂P) = (t : ℝ) := by sorry
