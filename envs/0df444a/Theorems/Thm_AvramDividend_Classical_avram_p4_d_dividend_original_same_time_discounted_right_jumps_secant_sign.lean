-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_same_time_discounted_right_jumps_secant_sign
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_same_time_discounted_right_jumps_secant_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:25:31.300518+00:00
-- url     : https://prove2.me/theorems/32678284-b30d-4018-94c6-b214848ca8df
-- title:
--   Actual original post-Lévy/pre-right-dividend discounted hjump correction is nonpositive at every eligible payment
-- statement:
--   Use the exact P4-F hjump secant premise in its own chronological source state, riskProcess X x D t (after the contemporaneous Lévy jump and before the right-continuous dividend jump). For any eligible time zero or strictly before ruin, prove that exp(−qt) multiplied by the complete cash-plus-value-loss rightpayment jump correction is nonpositive. This applies to simultaneous source and dividend jumps and the eligible inclusive horizon atom; the excluded positive ruin-time payment is left out correctly. The proof is independent of w smoothness and uses hjump explicitly.
-- source:
--   Canonical original P4-F hjump state, rightLimit and riskProcess; pinned Mathlib positive real exponential and linear arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_original_same_time_discounted_right_jumps_secant_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) +
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) -
          w (riskProcess X x D t ω)) ≤ 0 := by sorry
