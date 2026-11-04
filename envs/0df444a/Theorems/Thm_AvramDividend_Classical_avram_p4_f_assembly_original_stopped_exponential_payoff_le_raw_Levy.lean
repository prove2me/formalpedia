-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_exponential_payoff_le_raw_Levy
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_stopped_exponential_payoff_le_raw_Levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:23:48.899332+00:00
-- url     : https://prove2.me/theorems/7dec9d65-a24c-45ee-97c7-75089c1904ec
-- title:
--   Original stopped controlled reserve positive exponential moment is dominated pathwise by raw Lévy exponential
-- statement:
--   For every actual original admissible controlled dividend process, exact stopped postpayment-or-ruin W is pathwise at most the raw source x+Xτ. At nonnegative exponential parameter θ, exp(θW)≤exp(θ(x+Xτ)). This source-bound interface can be composed with existing accepted original exponential supermartingale/moment lemmas to handle terminal integrability at infinite cap under a justified growth comparison, with no new model or Brownian surrogate.
-- source:
--   Accepted P4-F original stopped W≤raw source X ddf76c68, pinned Mathlib Real.exp_le_exp and mul_le_mul_of_nonneg_left.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_W_le_source_X
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_stopped_exponential_payoff_le_raw_Levy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ ω, Real.exp (θ * W ω) ≤ Real.exp (θ * (x + X.X (τ ω) ω)) := by sorry
