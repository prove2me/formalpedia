-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_discounted_right_payment_remainder_nonpos
-- name    : AvramDividend.Classical.avram_p4_f6_original_discounted_right_payment_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:22:08.001981+00:00
-- url     : https://prove2.me/theorems/485cbe8d-d30f-4774-88db-3b99b589654d
-- title:
--   Original discounted right-dividend payment jump residual is nonpositive at zero and pre-ruin clocks
-- statement:
--   For the actual original controlled reserve and its right-limit dividend convention, the assumed source HJB jump inequality gives a nonpositive discounted jump residual at t=0 or any strictly pre-ruin time. The exponential discount is strictly positive, so the sign remains nonpositive. This is the exact payment remainder sign needed in the original stopped Ito–Meyer inequality, including an initial right-payment atom.
-- source:
--   Algebra from canonical hjump on riskProcess and Real.exp_pos, preserving same original process and rightLimit D - D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_original_discounted_right_payment_remainder_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω)) ≤ 0 := by sorry
