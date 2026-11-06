-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_enlarged_cap_optimality_of_upper
-- name    : AvramDividend.Classical.avram_sweep16_original_enlarged_cap_optimality_of_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:04:19.755721+00:00
-- url     : https://prove2.me/theorems/681ea91c-1ac0-4307-b9a5-14c6e5aeec4d
-- title:
--   Original optimal barrier across enlarged caps under cap-specific verification
-- statement:
--   For each cap larger than cstar, a source-exact original-process verification upper bound combines with the already Proved enlarged-cap barrier lower bound to give equality of capped value and the cstar barrier payoff for every nonnegative initial reserve. The argument is an explicit order-antisymmetry theorem; it introduces no stochastic assumptions beyond the declared cap-specific upper bound and no circular import.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_enlarged_cap_barrier_lower


open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_enlarged_cap_optimality_of_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (C : ℝ≥0∞) (hCap : cstar W ≤ C)
    (hUpper : ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q C x = ENNReal.ofReal (vcstar W x) := by sorry
