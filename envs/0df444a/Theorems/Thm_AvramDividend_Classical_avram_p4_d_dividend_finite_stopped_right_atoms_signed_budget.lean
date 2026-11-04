-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_finite_stopped_right_atoms_signed_budget
-- name    : AvramDividend.Classical.avram_p4_d_dividend_finite_stopped_right_atoms_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:22:58.736087+00:00
-- url     : https://prove2.me/theorems/800e9e5e-9d94-4736-98ab-b2b1b173ffb2
-- title:
--   Finite stopped original-source right-payment atoms satisfy the discounted signed budget
-- statement:
--   For any finite set of original right dividend payment times lying in the genuine capped finite time interval and eligible under strict ruin/time-zero paymentTimes semantics, apply the actual source hjump at the post-X prepayment reserve to each original right-jump atom. The sum of discounted cash plus postpayment minus prepayment value corrections is nonpositive. Includes initial, horizon and simultaneous source-payment jumps. This is a finite analogue of the required infinite jump signed remainder; countable summability is a separate obligation.
-- source:
--   Exact original rightLimit, riskProcess and hjump premises in original Itô residual UUID 0dda1be7; Finset.sum_nonpos and positive exponential.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_finite_stopped_right_atoms_signed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (ω : Ω) (T : ℝ≥0) (s : Finset ℝ≥0)
    (hstop : ∀ t ∈ s, (t : ℝ) ≤ (T : ℝ))
    (hactive : ∀ t ∈ s,
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ s, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω))) ≤ 0 := by sorry
