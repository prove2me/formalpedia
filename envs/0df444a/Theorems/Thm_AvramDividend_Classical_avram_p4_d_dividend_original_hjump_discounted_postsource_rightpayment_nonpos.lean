-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_hjump_discounted_postsource_rightpayment_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_hjump_discounted_postsource_rightpayment_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T19:00:21.104026+00:00
-- url     : https://prove2.me/theorems/ef7a3bb7-39e2-4e7e-b794-4b2adf3b8744
-- title:
--   Exact original P4-F hjump secant signs post-source right-dividend payments
-- statement:
--   Apply the canonical original-source P4-F right-dividend-jump secant hypothesis at the correct post-X-jump, pre-D-rightpayment riskProcess reserve. Every admissible zero-time or strictly pre-ruin rightpayment has a nonpositive discounted cash-plus-w increment, including simultaneous original Levy and dividend jumps and pre-ruin horizon payments. The source positive ruin rightpayment is excluded, and no replacement of hjump by a derivative condition is made.
-- source:
--   Exact canonical P4-F formal hjump premise of theorem 0dda1be7, original rightLimit D, riskProcess X x D and ruinTime, and Real.exp_pos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_hjump_discounted_postsource_rightpayment_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ) :
    Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω)) ≤ 0 := by sorry
