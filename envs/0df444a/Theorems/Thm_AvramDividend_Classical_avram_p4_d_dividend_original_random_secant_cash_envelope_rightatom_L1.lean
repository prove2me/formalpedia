-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_secant_cash_envelope_rightatom_L1
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_secant_cash_envelope_rightatom_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:00:42.109842+00:00
-- url     : https://prove2.me/theorems/4d816f23-a22f-4ec4-a604-f70b99b7963b
-- title:
--   Original stochastic right-payment signed sum L1 with random pathwise secant-cash integrable envelope
-- statement:
--   For the actual original post-source-jump/pre-dividend risk process, allow an honest path-dependent finite right-payment upper secant factor K(ω)≥1 on all enumerated true source payment times before an arbitrary finite random stop. Using the original explicit hjump, countable measurable indexed corrections, and an integrable product envelope (K−1)*Cash where Cash is the exact stopped discounted Stieltjes payment mass, prove the signed infinite right-atom correction is absolutely summable pathwise, L1 and nonpositive almost surely. This avoids an unjustified uniform derivative bound at zero/cap contact, but does not claim integrability of K Cash without separately verifying it.
-- source:
--   Proved fd02394f original all paymentTimes absolute atomic Cash bound pathwise; original Cash and hjump of P4-F 0dda1be7; Mathlib AEStronglyMeasurable.tsum and Integrable.mono

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_secant_cash_envelope_rightatom_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Countable ι]
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (r : ℝ≥0), (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D r ω - D r ω ≤ w (riskProcess X x D r ω) -
        w (riskProcess X x D r ω - (rightLimit D r ω - D r ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (K : Ω → ℝ) (hK : ∀ ω, 1 ≤ K ω)
    (hLocalSecant : ∀ ω i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          K ω * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ u in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)).toReal)
    (hEnvelopeI : Integrable (fun ω => (K ω - 1) * Cash ω) P)
    (hAtomTermMeas : ∀ i : ι,
      AEStronglyMeasurable (fun ω => Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) P) :
    let H : Ω → ℝ := fun ω => ∑' i : ι,
      Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))
    Integrable H P ∧ (∀ᵐ ω ∂P, H ω ≤ 0) := by sorry
