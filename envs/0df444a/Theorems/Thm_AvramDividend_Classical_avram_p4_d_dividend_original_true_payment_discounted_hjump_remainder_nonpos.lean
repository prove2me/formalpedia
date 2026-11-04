-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_payment_discounted_hjump_remainder_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_true_payment_discounted_hjump_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:01:08.602767+00:00
-- url     : https://prove2.me/theorems/69f058fb-f092-490e-9521-62dea55d985c
-- title:
--   At each true original payment the discounted source-ordered right-dividend hjump remainder is nonpositive
-- statement:
--   Original true paymentTimes membership gives exactly either time zero or strict preruin survival. The canonical original Itô–Meyer hypothesis hjump then applies at riskProcess X x D t, which is post the original X source jump and prior to the rightLimit dividend payment. Multiplication by the strictly positive discount exp(-qt) gives the nonpositive discounted right-dividend signed remainder, valid at simultaneous source and dividend jumps. No regularity or stochastic calculus hypothesis is introduced.
-- source:
--   Original canonical P4-F 0dda1be7 exact hjump and riskProcess ordering; source-proved paymentTimes zero-or-survival a7a447fa; Avram Proposition 4(i), Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At each original true payment, the actual discounted right-dividend budget is nonpositive,
    using the post-Lévy-jump reserve without swapping jump order. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_true_payment_discounted_hjump_remainder_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0)
    (hPay : (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)) :
    Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω)) ≤ 0 := by sorry
