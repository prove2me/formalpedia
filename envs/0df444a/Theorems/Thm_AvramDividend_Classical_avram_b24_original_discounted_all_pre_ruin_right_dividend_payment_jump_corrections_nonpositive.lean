-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_discounted_all_pre_ruin_right_dividend_payment_jump_corrections_nonpositive
-- name    : AvramDividend.Classical.avram_b24_original_discounted_all_pre_ruin_right_dividend_payment_jump_corrections_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:55:41.743714+00:00
-- url     : https://prove2.me/theorems/32f95ab5-eb88-4e51-8f59-f058a68cc613
-- title:
--   Actual original discounted dividend right-payment jump cash correction is nonpositive for every finite original pre-ruin payment mesh, including time zero
-- statement:
--   For the genuine original spectrally negative Lévy X and an actual dividend strategy D with the original pre-ruin (and time-zero) right-payment slope inequality, at every chosen original physical dividend payment clock t which is time zero or strictly before the true ruin clock, the paid right dividend atom Δ⁺D(t)=rightLimit D t-D t is bounded by the corresponding actual decrease of the candidate value w at the exact postpayment original reserve riskProcess X x D t. Hence the finite sum of discounted cash-minus-value-decrease corrections exp(-qt)[Δ⁺D-(w(Y_t)-w(Y_t-Δ⁺D))] across arbitrary finite right-payment times at or before the true pre-ruin horizon is nonpositive, without dropping the initial t=0 right payment or evaluating the inequality postruin. Each real discount exponential is positive for any real q, and the original pre-ruin payment hypothesis gives every summand nonpositive. This rigorously isolates the right-payment Stieltjes atom sign in B219 original finite-grid discounted Ito-Meyer cash ledger. It does not assert the missing continuous Stieltjes payment, Gaussian/mark gains, generator drift or terminal ruin contact corrections.
-- source:
--   Original B219 right-payment pre-ruin cash slope hypothesis, actual riskProcess and rightLimit D, finite physical nonpositive discounted cash correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_discounted_all_pre_ruin_right_dividend_payment_jump_corrections_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : Finset ℝ≥0)
    (hPre : ∀ t ∈ S,
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ S, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) -
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))))) ≤ 0 := by sorry
