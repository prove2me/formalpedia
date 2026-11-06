-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_zero_cstar_original_capped_optimality
-- name    : AvramDividend.Classical.avram_sweep16_zero_cstar_original_capped_optimality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:49:35.671802+00:00
-- url     : https://prove2.me/theorems/647c455a-838b-4175-99f7-ab8925c17446
-- title:
--   Original zero c* barrier is exactly optimal for every capped initial reserve
-- statement:
--   This is a source-exact complete special case of the optimal barrier conclusion. Under cstar W=0, the accepted zero-cap boundary value package and zero-cap value upper bound give the genuine original capped variational upper bound at every nonnegative reserve. The Proved barrier attainment theorem supplies an actual admissible zero-barrier dividend strategy achieving vcstar. Inserting that original witness into the defining double supremum gives the matching lower bound. The proof keeps the initial dividend atom and has no unproved BV/UBV stochastic assumptions.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital
import Theorems.Thm_AvramDividend_Classical_zero_cap_boundary_value_package
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_zero_cstar_original_capped_optimality
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : cstar W = 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x) := by sorry
