-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_unrestricted_upper_iff_all_cap_uppers
-- name    : AvramDividend.Classical.avram_sweep16_unrestricted_upper_iff_all_cap_uppers
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:10:40.473198+00:00
-- url     : https://prove2.me/theorems/02894fa4-2351-4d1c-be5a-df1df827ebcb
-- title:
--   Original unrestricted verification upper bound iff uniform capped verification
-- statement:
--   For any original spectrally negative Lévy process, capital x, discount q and bound M, bounding every capped dividend value by M is logically equivalent to bounding the unrestricted dividend value by M. The top-cap source equality proves the forward implication, and a separately proved direct capped-to-unrestricted strategy inclusion proves the converse. This supplies an exact original-process cap-to-global verification adapter without finite-cap approximation or extra hypotheses.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_capped_value_le_unrestricted_value
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_unrestricted_upper_iff_all_cap_uppers
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) (M : ℝ≥0∞) :
    (∀ C : ℝ≥0∞, valueFunctionLe X q C x ≤ M) ↔
      valueFunction X q x ≤ M := by sorry
