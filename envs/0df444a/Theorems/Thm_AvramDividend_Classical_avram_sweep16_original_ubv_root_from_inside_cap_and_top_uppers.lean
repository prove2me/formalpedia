-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_root_from_inside_cap_and_top_uppers
-- name    : AvramDividend.Classical.avram_sweep16_original_ubv_root_from_inside_cap_and_top_uppers
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:12:27.614223+00:00
-- url     : https://prove2.me/theorems/da9caa98-80f7-40b5-ad87-b9d8967ad991
-- title:
--   Original UBV classical c-star root reduces to within-cap and unrestricted upper bounds
-- statement:
--   A source-exact exact-shape original UBV root reduction using only Proved public parents. From the original local capped upper bound up to the actual c-star cap, the Proved above-cap extension yields the capped upper bound for all nonnegative initial reserves. The Proved barrier-attainment lower bound gives exact equality. The generator-conditional unrestricted upper bound is likewise sharpened to equality by the barrier lower bound. The Proved original-UBV zero-reserve root reduction then supplies all root clauses for nonnegative x, with no additional smoothness, artificial stochastic input, circular root import or axiom. The two explicitly stated upper inequalities are the remaining mathematical obligations, not claims already established.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_capped_value_all_capital_without_smoothness
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_root_suffices_strict_positive_reserve

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_ubv_root_from_inside_cap_and_top_uppers
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hInsideCap : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ cstar W →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x))
    (hTopUpper :
      (∀ y : ℝ, (cstar W).toReal < y →
        X.GeneratorIntegrable (vcstar W) y ∧
          X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 ≤ x →
        valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x)) ∧
      ((∀ y : ℝ, (cstar W).toReal < y →
          X.GeneratorIntegrable (vcstar W) y ∧
            X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by sorry
