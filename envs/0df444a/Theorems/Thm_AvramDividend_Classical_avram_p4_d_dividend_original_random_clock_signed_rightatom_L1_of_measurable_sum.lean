-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_signed_rightatom_L1_of_measurable_sum
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_signed_rightatom_L1_of_measurable_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:38:39.722996+00:00
-- url     : https://prove2.me/theorems/3fa11cd7-43ab-49db-8bce-b6eaf91d293d
-- title:
--   Original stopped source-ordered right-payment sum is integrable under measurable enumeration and true Cash L1
-- statement:
--   For actual post-Lévy, pre-dividend risk reserve, assume an honest pointwise injection of selected right-dividend payment times into the original paymentTimes up to the sample-dependent stop. With exact hjump, a uniform local secant constant K≥1, true source Stieltjes Cash and its integrability, and explicit AEStronglyMeasurable of the signed atomic total, prove that the signed atomic sum is integrable and nonpositive almost surely. The proof must derive its envelope from the accepted absolute-series right-atom lemma, retaining time-zero and horizon atoms where eligible. No measurability of arbitrary random enumeration is inferred.
-- source:
--   Original P4-F 0dda1be7 canonical Cash and hjump; Proved 1be1b311 exact random-clock absolute atomic series; Proved d9f85ad8 original cash-dominated L1 interface; Avram-Palmowski-Pistorius Proposition 4(i), Eq 5.13

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_ae_rightatom_absolute_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cash_dominates_integrable_negative_residual
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_signed_rightatom_L1_of_measurable_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0), (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ ω i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          K * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash Hatom : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hHatom : ∀ ω, Hatom ω = ∑' i : ι,
      Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω)))
    (hHatomMeas : AEStronglyMeasurable Hatom P) :
    Integrable Hatom P ∧ (∀ᵐ ω ∂P, Hatom ω ≤ 0) := by sorry
