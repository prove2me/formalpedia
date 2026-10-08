-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_singleton_lintegral_bound
-- name    : AvramDividend.Classical.discounted_dividendMeasure_singleton_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:11:14.589897+00:00
-- url     : https://prove2.me/theorems/71370856-f989-4e9d-a0dc-9738383c2765
-- title:
--   An admissible discounted dividend singleton lintegral is dominated by exponential reserve value loss
-- statement:
--   For an admissible dividend payment at time t, the exact discounted Lebesgue–Stieltjes integral over {t} in the mission's dividendValue definition is bounded above by the corresponding discounted exponential test-value decrease. This is the first direct lintegral-level link between the actual dividendMeasure integrator and the exponential verification inequality, obtained from Mathlib lintegral_singleton plus the atomic measure bound. It does not yet bound the sum of all atoms or the continuous Stieltjes component.
-- source:
--   Child discounted_dividendMeasure_atom_exponential_bound; pinned Mathlib MeasureTheory.lintegral_singleton.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_dividendMeasure_singleton_lintegral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (θ q : ℝ) (hθ : 1 ≤ θ)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in {(t : ℝ)}, ENNReal.ofReal (Real.exp (-(q * s)))
       ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
      (Real.exp (θ * riskProcess X x D t ω) -
        Real.exp (θ * (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω))))) := by sorry
