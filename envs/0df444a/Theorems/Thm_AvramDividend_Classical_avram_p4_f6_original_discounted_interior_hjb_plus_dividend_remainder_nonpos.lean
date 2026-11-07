-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_discounted_interior_hjb_plus_dividend_remainder_nonpos
-- name    : AvramDividend.Classical.avram_p4_f6_original_discounted_interior_hjb_plus_dividend_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:25:28.070599+00:00
-- url     : https://prove2.me/theorems/074ff6e9-75ce-472b-8081-89b1b95544cf
-- title:
--   Discounted original strict-interior generator plus right-dividend residual is nonpositive
-- statement:
--   At an actual original Lévy path time zero or strictly prior to ruin, when the post-right-dividend reserve is in the positive cap interior, the source HJB generator drift and right-payment remainder are each nonpositive. Their sum, weighted by the positive discount factor, is nonpositive. This packages the precise finite-clock source drift and payment inequalities without pretending to have proved the compensated martingale identity.
-- source:
--   Apply actual hw_gen to the postpayment controlled reserve, actual hjump to riskProcess X x D, and Real.exp positivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_original_discounted_interior_hjb_plus_dividend_remainder_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (hy : 0 < x + X.X t ω - rightLimit D t ω)
    (hyC : ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) < C) :
    Real.exp (-(q * (t : ℝ))) *
      ((X.generator w (x + X.X t ω - rightLimit D t ω) -
        q * w (x + X.X t ω - rightLimit D t ω)) +
       ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω))) ≤ 0 := by sorry
