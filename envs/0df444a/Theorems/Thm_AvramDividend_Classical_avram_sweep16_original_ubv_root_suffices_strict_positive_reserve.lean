-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_root_suffices_strict_positive_reserve
-- name    : AvramDividend.Classical.avram_sweep16_original_ubv_root_suffices_strict_positive_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:46:33.243318+00:00
-- url     : https://prove2.me/theorems/c6ea2188-012a-492e-9d7c-f4cfa5cbb7fd
-- title:
--   Original unbounded-variation full classical barrier root reduces to strict positive initial reserve
-- statement:
--   Source-exact root-shaped unbounded-variation reduction. Under the two remaining strictly positive-reserve original optimal-value assertions, reconstruct all three original c-star root conjunctions for every nonnegative reserve. At positive reserves, the already Proved barrier-attainment theorem supplies original admissibility and exact dividend reward. The zero-reserve case is discharged by the newly Proved/public original unbounded-variation full root branch, with no stochastic assumptions or unstated equality-in-law. The HJB generator premise for unrestricted optimality is preserved exactly. No root theorem, local_verification or other Open parent is imported.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_complete_root_at_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_ubv_root_suffices_strict_positive_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hCapPositive : ∀ x : ℝ, 0 < x →
      valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x))
    (hTopPositive :
      (∀ y : ℝ, (cstar W).toReal < y →
        X.GeneratorIntegrable (vcstar W) y ∧
          X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 < x →
        valueFunction X q x = ENNReal.ofReal (vcstar W x)) :
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
