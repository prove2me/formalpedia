-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_allvariation_root_from_inside_cap_and_top_upper
-- name    : AvramDividend.Classical.avram_sweep16_original_allvariation_root_from_inside_cap_and_top_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:18:25.850326+00:00
-- url     : https://prove2.me/theorems/6b1a22cc-93d5-486c-bfc5-ade83bb5e4a7
-- title:
--   Original classical barrier optimality in both variation regimes from inside-cap and top value uppers
-- statement:
--   A source-exact exact-shape classical optimality root reduction valid for both bounded and unbounded variation with no additional C1/C2 smoothness or stochastic hypotheses. If the original capped value bound holds within the actual finite c-star cap, the Proved cap-extension lemma gives it for every nonnegative capital. The Proved barrier-attainment and original capped/unrestricted lower bounds then sharpen both the capped and generator-conditional unrestricted value inequalities to equalities, providing all original root clauses. Every imported theorem is already Proved and public; there is no circular import or root premise.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_capped_value_all_capital_without_smoothness
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_allvariation_root_from_inside_cap_and_top_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
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
