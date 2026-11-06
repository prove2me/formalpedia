-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_horizon_pre_rightpayment_secant_sign
-- name    : AvramDividend.Classical.avram_p3_grid4_original_horizon_pre_rightpayment_secant_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:12:04.673024+00:00
-- url     : https://prove2.me/theorems/94b26df8-8d70-4136-b062-f02192f0aaca
-- title:
--   Original strictly surviving horizon terminal nonnegative and secant-dominating rightpayment plus postpayment value
-- statement:
--   On the original X/D paths, strictly surviving through the deterministic positive horizon makes its discounted pre-rightpayment terminal nonnegative and dominates the discounted horizon dividend jump plus postpayment continuation via the exact rightLimit D secant. Both branch values vanish when survival fails. This proves the horizon rightpayment terminal sign, with no assumption of zero horizon payment or w(0)=0.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_horizon_pre_rightpayment_secant_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (w : ℝ → ℝ)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∀ ω,
      0 ≤ (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)) ∧
    (∀ ω,
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          (rightLimit D S ω - D S ω) +
        Real.exp (-(q * T)) *
          w (riskProcess X x D S ω -
            (rightLimit D S ω - D S ω))
      else 0) ≤
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)) := by sorry
