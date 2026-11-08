-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_approximate_mean_zero_budget_implies_expected_upper
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_approximate_mean_zero_budget_implies_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:22:31.807526+00:00
-- url     : https://prove2.me/theorems/1b1a7371-ef7f-4135-b16f-ae8b2430ecb7
-- title:
--   Original finite-cap stopped payoff upper bound from centred approximants with vanishing signed L1 error
-- statement:
--   For the exact original Levy stopped payoff F at each stopping subclock sigma no later than the ruin-limited horizon, suppose there are integrable zero-mean martingale approximants and integrable signed errors with expected errors converging to zero, and a pathwise almost-everywhere upper Ito budget at every approximation level. Then the expected stopped payoff is at most the candidate value at the initial surplus. The original process, post-right-payment reserve and inclusive dividend-cash source are preserved literally. This expectation transfer does not assume the stochastic Ito identity or vanishing-error construction, which remain separate proof obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_approximate_mean_zero_budget_implies_expected_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (σ : ℕ → Ω → ℝ≥0) (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hApprox : ∀ k, ∃ M Err : ℕ → Ω → ℝ,
      (∀ j, Integrable (M j) P ∧ (∫ ω, M j ω ∂P) = 0) ∧
      (∀ j, Integrable (Err j) P) ∧
      Tendsto (fun j => ∫ ω, Err j ω ∂P) atTop (nhds (0 : ℝ)) ∧
      (∀ j, ∀ᵐ ω ∂P,
        F k ω ≤ w x + M j ω + Err j ω)) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by sorry
