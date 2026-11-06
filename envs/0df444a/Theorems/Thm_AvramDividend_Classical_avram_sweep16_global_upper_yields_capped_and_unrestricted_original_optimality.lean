-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_global_upper_yields_capped_and_unrestricted_original_optimality
-- name    : AvramDividend.Classical.avram_sweep16_global_upper_yields_capped_and_unrestricted_original_optimality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:14:25.195007+00:00
-- url     : https://prove2.me/theorems/34f71da4-5d3d-416c-85f8-635f1661f988
-- title:
--   Original cstar capped and unrestricted optimality from one unrestricted verification upper bound
-- statement:
--   Suppose the unrestricted original value-function upper bound by vcstar is available at every nonnegative reserve. Inclusion of original admissible strategies with cap cstar into the unrestricted admissible class supplies the capped upper bound by an explicit pair of nested iSup inequalities. The independently Proved barrier attainment lower-bound theorem supplies the reverse inequalities for capped and unrestricted values. Antisymmetry proves both desired optimality equalities at once. This reduction is source-exact and makes no claim that the upper bound has already been proved.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_global_upper_yields_capped_and_unrestricted_original_optimality
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (hUpper : ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x) ∧
      valueFunction X q x = ENNReal.ofReal (vcstar W x) := by sorry
