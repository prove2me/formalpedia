-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_discounted_rightpayment_signed_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_discounted_rightpayment_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:25:06.692055+00:00
-- url     : https://prove2.me/theorems/c99fb4f1-69d2-4650-82b7-97886842b935
-- title:
--   Discounted original right-dividend signed Ito remainder is nonpositive at active payment times
-- statement:
--   For the exact original hjump condition, at any payment time zero or strictly before ruin, the discounted signed right-payment residual exp(-qt)[(D_{t+}-D_t)+w(x+X_t-D_{t+})-w(x+X_t-D_t)] is nonpositive. This uses the post-source-jump prepayment reserve and works at time zero, simultaneous source and dividend jumps and the horizon if active. It makes no unjustified interior differentiability or boundary-extension claim.
-- source:
--   Original hjump hypothesis in canonical UUID 0dda1be7-9d8b-41e0-ae51-55fab5c38e22, exact source riskProcess and rightLimit definitions, Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postsource_rightpayment_reserve_eq
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_discounted_rightpayment_signed_nonpos
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
    (ω : Ω) (t : ℝ≥0)
    (hactive : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ) :
    Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω)) ≤ 0 := by sorry
