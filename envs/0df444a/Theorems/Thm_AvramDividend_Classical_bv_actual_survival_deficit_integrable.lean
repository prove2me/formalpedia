-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_survival_deficit_integrable
-- name    : AvramDividend.Classical.bv_actual_survival_deficit_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:18:57.593561+00:00
-- url     : https://prove2.me/theorems/8e7ec077-fd7e-4c89-b59d-1ce701d418d9
-- title:
--   Actual BV Lévy zero-barrier strict-survival deficit has finite expectation unconditionally from canonical adaptedness and origin
-- statement:
--   Under the standing and bounded-variation assumptions, the actual Lévy drift deficit restricted to the genuine strict zero-barrier survival event is Bochner integrable for every nonnegative horizon. No separately imposed sample-path origin or measurability assumptions are needed: X.X_zero supplies the pathwise origin, adaptedness makes X_T measurable, the accepted barrierRuinTime_measurable theorem makes strict survival measurable, and the indicated deficit is measurable. Apply the previously proved bounded survival-restricted deficit integrability theorem. This is critical to the infinite-activity reflected-dividend valuation without large-jump moment assumptions.
-- source:
--   Canonical SpectrallyNegativeLevy.X_zero and adapted fields, MeasureTheory.Adapted.measurable, barrierRuinTime_measurable and proved bv_actual_survival_deficit_integrable_of_origin_zero.

import Theorems.Thm_AvramDividend_Classical_bv_actual_survival_deficit_integrable_of_origin_zero
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_survival_deficit_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    Integrable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => (T : ℝ) * X.drift - X.X T ω)) P := by sorry
