-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_hjump_positive_stopped_rightpayment_tsum_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_hjump_positive_stopped_rightpayment_tsum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T19:04:44.384621+00:00
-- url     : https://prove2.me/theorems/0c5e4dc2-d67e-4508-85d0-b2f2595b6b29
-- title:
--   Actual original hjump source secant signs the entire summable stopped rightpayment set
-- statement:
--   The original P4-F right-dividend-jump secant hjump, applied at the true post-X-jump and pre-right-D payment reserve, makes every discounted rightpayment summand nonpositive at time zero or strictly before actual ruin. For any original stopped right-payment time set B satisfying that clock condition, with the genuine summability hypothesis retained, the complete real chronological right-payment residual sum is nonpositive. This handles simultaneous source/payment jumps and eligible observation-horizon rightpayments but excludes positive ruin-time payments by source convention.
-- source:
--   Accepted literal P4-F hjump secant sign helper ef7a3bb7 and pinned Mathlib tsum_nonpos under the original full-stopped rightpayment summability interface.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_hjump_discounted_postsource_rightpayment_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_hjump_positive_stopped_rightpayment_tsum_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (B : Set ℝ≥0)
    (hB : ∀ t : B,
      (t : ℝ≥0) = 0 ∨ ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hSummable : Summable (fun t : B =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∑' t : B, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by sorry
