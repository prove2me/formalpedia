-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:46:21.564328+00:00
-- url     : https://prove2.me/theorems/9f4070e7-1cc5-4410-83fb-bd63d7b99855
-- title:
--   Exact original post-source right-dividend discount residual is nonpositive at zero or strictly before ruin
-- statement:
--   Use the original theorem's explicit hjump on the precise post-Levy-source-jump, pre-dividend-payment reserve. By expanding original riskProcess, the postpayment reserve equals x+X.X(t)-rightLimit D(t), even when the source and dividend jump simultaneously. At a zero or strictly pre-ruin stopped time, the discounted payment atom plus test-function loss is nonpositive. This statement covers an eligible terminal horizon atom and initial payment; positive-time ruin is excluded by the original paymentTimes predicate. The source measure-to-atom equality is separately Proved and must be used for aggregate cash.
-- source:
--   Avram, Palmowski and Pistorius Proposition 4(i), equation (5.13); exact original hjump in 0dda1be7-9d8b-41e0-ae51-55fab5c38e22 and source riskProcess/rightLimit definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (τ : Ω → ℝ≥0) (ω : Ω)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    Real.exp (-(q * (τ ω : ℝ))) *
      ((rightLimit D (τ ω) ω - D (τ ω) ω) +
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) -
        w (riskProcess X x D (τ ω) ω)) ≤ 0 := by sorry
