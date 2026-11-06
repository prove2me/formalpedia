-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_zero_reserve_unrestricted_value
-- name    : AvramDividend.Classical.avram_sweep16_original_ubv_zero_reserve_unrestricted_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:53:13.553641+00:00
-- url     : https://prove2.me/theorems/01274272-94e9-4610-ab54-0b761dd9991a
-- title:
--   Original unbounded-variation zero initial reserve has zero unrestricted perpetual dividend value
-- statement:
--   Original-process unrestricted UBV value at reserve zero. The accepted
--   unbounded-variation zero-start theorem proves zero dividend value for every
--   admissible strategy under every cap. Instantiating the cap at top and using
--   the accepted exact cap-at-top identity gives the unrestricted perpetual
--   valueFunction at initial capital zero, with no HJB or smoothness premise.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_ubv_zero_reserve_unrestricted_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) :
    valueFunction X q 0 = 0 := by sorry
