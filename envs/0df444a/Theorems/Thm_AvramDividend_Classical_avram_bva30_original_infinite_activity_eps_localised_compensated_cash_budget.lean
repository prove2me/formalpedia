-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva30_original_infinite_activity_eps_localised_compensated_cash_budget
-- name    : AvramDividend.Classical.avram_bva30_original_infinite_activity_eps_localised_compensated_cash_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T08:04:25.692826+00:00
-- url     : https://prove2.me/theorems/bcb5f5e5-6b5a-47cd-a2bd-0e38afcb7c60
-- title:
--   Original infinite-activity BV cash bound via epsilon-localised integrable compensated gains
-- statement:
--   For any fixed strict T-T/(n+2) dividend-cash horizon, full surviving postpayment T reward and positive error epsilon, construct on the SAME original X, D and P an integrable compensated gain with nonpositive unconditional mean, and a physical pathwise payoff upper bound by w(x)+M+epsilon. The epsilon absorbs compact-band localisation and integrable small-negative-jump truncation without unsupported global generator L1. Respect reserve zero, time-zero right payments, common jump/payment times, ruin and T.
-- source:
--   Epsilon-localisation alternative to the exact original infinite-activity cash theorem d1728964

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva30_original_infinite_activity_eps_localised_compensated_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ M : Ω → ℝ, Integrable (F n) P ∧ Integrable M P ∧
        (∫ ω, M ω ∂P) ≤ 0 ∧
        (∀ᵐ ω ∂P, F n ω ≤ w x + M ω + ε) := by sorry
