-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_all_enlarged_caps_optimal_of_global_upper
-- name    : AvramDividend.Classical.avram_sweep16_all_enlarged_caps_optimal_of_global_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:06:23.809203+00:00
-- url     : https://prove2.me/theorems/01f185da-5f80-4c21-9ce9-4b176ffe0bed
-- title:
--   Original enlarged-cap optimality from one unrestricted upper verification
-- statement:
--   For an original spectrally negative Lévy process satisfying standing conditions, one unrestricted verification upper bound implies exact value equality for every dividend cap C no smaller than the barrier cstar. The proof uses the already proved original capped-to-unrestricted value comparison and the already proved original enlarged-cap barrier lower bound, with no stochastic source assumptions beyond the stated global upper bound.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_enlarged_cap_barrier_lower
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_capped_value_le_unrestricted_value

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_all_enlarged_caps_optimal_of_global_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hUpper : ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ C : ℝ≥0∞, cstar W ≤ C →
      ∀ x : ℝ, 0 ≤ x →
        valueFunctionLe X q C x = ENNReal.ofReal (vcstar W x) := by sorry
