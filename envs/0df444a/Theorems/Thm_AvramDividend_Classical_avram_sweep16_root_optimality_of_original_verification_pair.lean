-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_root_optimality_of_original_verification_pair
-- name    : AvramDividend.Classical.avram_sweep16_root_optimality_of_original_verification_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:39:37.925908+00:00
-- url     : https://prove2.me/theorems/eb75e1c3-2189-40f6-8e6b-28658838966a
-- title:
--   Exact Avram cstar optimality from the explicit original upper verification pair
-- statement:
--   Source-exact integration of the complete canonical Avram optimality conclusion under a single explicit pair of original capped and unrestricted upper-verification inequalities. Derive cstar finiteness from the Proved cstar_lt_top theorem; the source barrier-attainment theorem establishes the actual admissible policy and exact dividend value. The previously kernel-Proved original barrier lower-bound theorem supplies the reverse capped and unrestricted supremum inequalities. Two antisymmetry arguments discharge both equalities. No reliance on Open local verification, original stopped stochastic residuals, equality in law, sorry or new axioms. The still-missing upper-verification pair remains an explicit premise.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_root_optimality_of_original_verification_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hUpper :
      (∀ x : ℝ, 0 ≤ x →
        valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) ∧
      ((∀ y : ℝ, (cstar W).toReal < y →
          X.GeneratorIntegrable (vcstar W) y ∧
            X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          valueFunction X q x ≤ ENNReal.ofReal (vcstar W x))) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x)) ∧
      ((∀ x : ℝ, (cstar W).toReal < x →
          X.GeneratorIntegrable (vcstar W) x ∧
            X.generator (vcstar W) x - q * vcstar W x ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by sorry
