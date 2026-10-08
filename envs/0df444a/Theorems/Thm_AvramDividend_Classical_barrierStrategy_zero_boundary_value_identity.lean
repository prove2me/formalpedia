-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity
-- name    : AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:31:01.566016+00:00
-- url     : https://prove2.me/theorems/c2921c8c-bf0f-407f-9d75-c154bb4ce6ea
-- title:
--   Zero-barrier reflection dividend value equals its scale-function boundary formula
-- statement:
--   For zero reserve and barrier zero, the expected discounted dividends of the reflected Lévy process coincide with the zero-barrier scale-function formula, including W'(0+) expressed as derivZeroPlus and divE and including the time-zero Stieltjes dividend atom. This is the probabilistic component of Proposition 1 at the degenerate barrier and is logically independent of the elementary nonnegativity property.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, equations (3.13)-(3.14), boundary a=0; dividendValue and scaleDeriv definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem barrierStrategy_zero_boundary_value_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by sorry

end AvramDividend.Classical
