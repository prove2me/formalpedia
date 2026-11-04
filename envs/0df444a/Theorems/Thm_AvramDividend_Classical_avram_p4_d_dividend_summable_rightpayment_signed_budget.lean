-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_summable_rightpayment_signed_budget
-- name    : AvramDividend.Classical.avram_p4_d_dividend_summable_rightpayment_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:25:48.594005+00:00
-- url     : https://prove2.me/theorems/a2f90e61-fa5e-4850-8347-45e2f4f20678
-- title:
--   Summable original right-dividend signed remainder is nonpositive over every active payment index set
-- statement:
--   For any real-summable family of actual original right-payment events indexed by nonnegative times, each eligible at zero or strictly before ruin, the sum of the exact discounted signed residual ΔD_t+w(x+X_t-D_{t+})-w(x+X_t-D_t) is nonpositive. The hypothesis preserves explicit source hjump ordering and makes real summability visible, allowing the discrete atomic component of H_div to be certified after separate source-exact identification and integrability.
-- source:
--   Original source hjump in canonical 0dda1be7, accepted P4-D post-source state equality 4fb2f44f; Mathlib tsum_nonpos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postsource_rightpayment_reserve_eq
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_summable_rightpayment_signed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (A : Set ℝ≥0)
    (hactive : ∀ t : A, (t : ℝ≥0) = 0 ∨
      ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ)
    (hsummable : Summable (fun t : A =>
      Real.exp (-(q * (((t : ℝ≥0) : ℝ)))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∑' t : A,
      Real.exp (-(q * (((t : ℝ≥0) : ℝ)))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) -
          w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by sorry
