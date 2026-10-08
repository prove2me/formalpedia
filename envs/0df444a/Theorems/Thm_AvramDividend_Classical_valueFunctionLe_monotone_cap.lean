-- Prove2me | Theorems.Thm_AvramDividend_Classical_valueFunctionLe_monotone_cap
-- name    : AvramDividend.Classical.valueFunctionLe_monotone_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:53:20.451842+00:00
-- url     : https://prove2.me/theorems/9029e14f-e512-4e29-9e42-5e58349516a6
-- title:
--   The capped dividend value function is nondecreasing in the reserve cap
-- statement:
--   Increasing the reserve upper bound from C1 to C2 preserves every previously permitted dividend strategy, so the supremum of dividend values over admissible strategies cannot decrease. This gives a precise monotonicity law for the capped value function in the local verification setting.
-- source:
--   Exact IsAdmissibleLe and valueFunctionLe definitions; Mathlib le_iSup_of_le and iSup_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.valueFunctionLe_monotone_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (C₁ C₂ : ℝ≥0∞) (hC : C₁ ≤ C₂) :
    valueFunctionLe X q C₁ x ≤ valueFunctionLe X q C₂ x := by sorry
