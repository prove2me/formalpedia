-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_capped_value_le_unrestricted_value
-- name    : AvramDividend.Classical.avram_sweep16_original_capped_value_le_unrestricted_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:07:03.312208+00:00
-- url     : https://prove2.me/theorems/3d330cb4-5010-4c7c-8076-cf3a7f6ed41a
-- title:
--   Original capped dividend value is bounded by the unrestricted dividend value
-- statement:
--   For an original spectrally negative Lévy dividend model, each capped admissible dividend strategy remains admissible without the cap. The original capped valueFunctionLe is an iSup over a subset of the admissible strategies defining valueFunction. The resulting order holds uniformly in the cap, reserve, discount rate and process, with no stochastic verification assumptions.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_capped_value_le_unrestricted_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (C : ℝ≥0∞) :
    valueFunctionLe X q C x ≤ valueFunction X q x := by sorry
