-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissibleCap_dividendValue_le_of_gradient_stochastic_budget
-- name    : AvramDividend.Classical.admissibleCap_dividendValue_le_of_gradient_stochastic_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:56:21.094057+00:00
-- url     : https://prove2.me/theorems/11b4e88d-d9e2-432f-a876-4f83cd4a13db
-- title:
--   Capped admissible dividend verification from derivative one and stochastic budget
-- statement:
--   The capped-admissible control hypothesis implies the uncapped admissibility and strategy properties. Combined with an interior derivative lower bound and exact expected stochastic interior-plus-boundary budget at each horizon, it bounds the complete infinite-horizon discounted dividend value, with the same native IsAdmissibleLe shape as the BV verification target.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_gradient_stochastic_interior_boundary_budget

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissibleCap_dividendValue_le_of_gradient_stochastic_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 ≤ q)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u : Ω → ℝ → ℝ)
    (hInterior : ∀ ω, MeasurableSet
      {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C})
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω,
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ)) ∩
          {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
          ENNReal.ofReal (Real.exp (-(q * t)) * deriv w (u ω t))
            ∂(dividendMeasure D ω)) +
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ)) \
          {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) ∂P) ≤ ENNReal.ofReal (w x)) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
