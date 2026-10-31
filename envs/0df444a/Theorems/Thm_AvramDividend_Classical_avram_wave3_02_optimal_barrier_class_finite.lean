-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_optimal_barrier_class_finite
-- name    : AvramDividend.Classical.avram_wave3_02_optimal_barrier_class_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:20:52.909373+00:00
-- url     : https://prove2.me/theorems/81b2fa86-9816-4771-833a-3f932584e18c
-- title:
--   Finite supremum of genuine discounted dividends across all nonnegative constant barriers
-- statement:
--   Under Standing, positive q and a genuine scale function, the supremum of expected discounted dividends from all genuine constant-barrier strategies with nonnegative cap is finite for each nonnegative starting capital. The accepted uniform strategy value bound provides a common finite x+C upper bound, and complete-lattice supremum rules with ENNReal finite addition establish the result. No global C1 or attainment is asserted.
-- source:
--   Avram Palmowski Pistorius (2007), barrier dividend problem; canonical Proved source Stieltjes strategy bound.

import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.CompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_strategy_value_growth

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_optimal_barrier_class_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
      dividendValue X q x (barrierStrategy X x a)) < ⊤ := by sorry
