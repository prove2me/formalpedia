-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package
-- name    : AvramDividend.Classical.barrier_zero_boundary_value_package
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T20:49:48.148501+00:00
-- url     : https://prove2.me/theorems/027a50fd-b61d-4033-9fd7-d3b97fe2f5e2
-- title:
--   Boundary value package for the zero barrier
-- statement:
--   At the zero barrier and zero initial reserve, the formal barrier candidate is nonnegative and equals the expected discounted dividends of the zero-barrier reflection strategy. This is the boundary case needed to extend Proposition 1 to a=0 and arbitrary nonnegative initial capital by splitting off the initial excess.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 and the zero-barrier convention discussed around pp. 8 and 13-15. This child isolates the boundary a=0 case that is excluded by the printed positive-barrier derivative formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem barrier_zero_boundary_value_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by
  sorry

end AvramDividend.Classical
