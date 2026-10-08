-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_nonneg
-- name    : AvramDividend.Classical.barrier_zero_boundary_value_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:30:31.185381+00:00
-- url     : https://prove2.me/theorems/df5df3b8-8ec5-4231-85d3-2263c3b9e822
-- title:
--   Zero-barrier boundary value and nonnegativity
-- statement:
--   At the zero barrier, started from zero, the expected discounted dividends of reflection equal the zero-barrier scale-function boundary formula W(0)/W'(0+) under the formal scaleDeriv/divE convention, and this real boundary value is nonnegative. This is the endpoint counterpart of Proposition 1 and equation (3.13), needed for the c*=0 case of Theorem 2.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 and the zero-barrier/right-derivative convention discussed around pp.8 and 13-15.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_zero_boundary_value_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by sorry

end AvramDividend.Classical
