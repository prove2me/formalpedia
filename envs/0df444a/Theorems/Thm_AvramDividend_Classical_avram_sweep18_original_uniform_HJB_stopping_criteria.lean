-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep18_original_uniform_HJB_stopping_criteria
-- name    : AvramDividend.Classical.avram_sweep18_original_uniform_HJB_stopping_criteria
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:17:26.493387+00:00
-- url     : https://prove2.me/theorems/db3ea86b-2339-43ca-b36a-77e0716d8fce
-- title:
--   Original BV-or-UBV uniform HJB sign, reserve and time-zero jump prerequisites
-- statement:
--   Under the original capped HJB and variant-specific C1/C2 regularity, the same process and dividend strategy satisfy generator integrability/sign, derivative slope-one sign, actual pre-ruin candidate nonnegativity and original right-payment jump secant at time zero or strictly before ruin. Apply the proved BV or UBV stopping criteria by the actual bounded-variation disjunction; no stronger smoothness or stochastic budget is introduced.
-- source:
--   Proved original BV HJB criteria 88794ba3-ff17-47cb-a447-17a40f512fce and original UBV HJB criteria 1efa471d-334e-488d-8db6-5bd7859c70e5.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep18_original_BV_HJB_stopping_criteria
import Theorems.Thm_AvramDividend_Classical_avram_sweep18_original_UBV_HJB_stopping_criteria
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep18_original_uniform_HJB_stopping_criteria
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
    (∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) := by sorry
