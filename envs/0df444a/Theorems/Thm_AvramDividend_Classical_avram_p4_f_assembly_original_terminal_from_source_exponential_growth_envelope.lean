-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_from_source_exponential_growth_envelope
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_terminal_from_source_exponential_growth_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:50:35.201601+00:00
-- url     : https://prove2.me/theorems/ed63338c-28e6-4b58-9446-f2269b0d1fcd
-- title:
--   Exact original stopped dividend terminal inherits a raw Lévy exponential growth envelope
-- statement:
--   For the genuine X,D stopped postpayment/ruin W and discounted Term, if the candidate w has a separately justified global exponential upper bound w(y)≤K exp(θy), the source terminal is bounded by the discounted raw Lévy exponential. The source X remains the original process, no new stochastic model is assumed. The growth premise is explicit, not derived from the canonical HJB assumptions; random-clock exponential integrability also remains to prove.
-- source:
--   Accepted original source exp W≤exp(x+Xτ) bound 7dec9d65; Mathlib mul_le_mul_of_nonneg_left and exp positivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_exponential_payoff_le_raw_Levy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_terminal_from_source_exponential_growth_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (q θ K : ℝ) (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hwGrowth : ∀ y : ℝ, w y ≤ K * Real.exp (θ * y))
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, Term ω ≤
      Real.exp (-(q * (τ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (τ ω) ω))) := by sorry
