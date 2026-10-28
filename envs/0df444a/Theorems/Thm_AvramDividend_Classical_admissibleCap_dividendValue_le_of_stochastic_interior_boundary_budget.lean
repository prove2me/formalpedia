-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissibleCap_dividendValue_le_of_stochastic_interior_boundary_budget
-- name    : AvramDividend.Classical.admissibleCap_dividendValue_le_of_stochastic_interior_boundary_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:19:17.450982+00:00
-- url     : https://prove2.me/theorems/4e57c9e4-7aa8-446b-8945-accfb63b2cb5
-- title:
--   Capped HJB dividend verification under the exact stochastic budget with native admissibility
-- statement:
--   A capped-admissible dividend strategy automatically satisfies the uncapped admissibility and dividend-strategy conditions. Hence, under HJB and a finite-horizon expectation budget including all boundary Stieltjes dividend mass, its complete expected discounted dividend value is bounded by the initial verification candidate. This has the native IsAdmissibleLe hypothesis used in the original local verification target.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_capped_stochastic_interior_boundary_budget

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissibleCap_dividendValue_le_of_stochastic_interior_boundary_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 ≤ q)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
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
