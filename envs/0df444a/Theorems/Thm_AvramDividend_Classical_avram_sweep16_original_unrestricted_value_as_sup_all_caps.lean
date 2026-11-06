-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_unrestricted_value_as_sup_all_caps
-- name    : AvramDividend.Classical.avram_sweep16_original_unrestricted_value_as_sup_all_caps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:09:19.600208+00:00
-- url     : https://prove2.me/theorems/3d732368-ab64-4c1e-9212-96bf94fa7210
-- title:
--   Original unrestricted dividend value equals supremum of all capped values
-- statement:
--   For each original spectrally negative Lévy process and starting capital, the unrestricted dividend value equals the supremum over all ENNReal payout caps, including the top cap. The forward inequality uses a separately proved direct admissible-strategy witness embedding; the reverse uses the separately proved top-cap equality. This accounts explicitly for C=top without requiring an unproved finite-cap exhaustion.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_capped_value_le_unrestricted_value
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_unrestricted_value_as_sup_all_caps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) :
    (⨆ C : ℝ≥0∞, valueFunctionLe X q C x) = valueFunction X q x := by sorry
