-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_zero_zero_nonneg
-- name    : AvramDividend.Classical.barrierValue_zero_zero_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T21:02:17.418981+00:00
-- url     : https://prove2.me/theorems/eb66042a-0dc2-4d0c-9514-5dd05be55c16
-- title:
--   Nonnegativity of the zero-barrier candidate at the origin
-- statement:
--   The zero-barrier candidate at zero is nonnegative. Its numerator W(0) is nonnegative by the scale-function axioms, and its extended right-derivative denominator is nonnegative because W' is nonnegative on the positive half-line and derivZeroPlus is the right liminf.
-- source:
--   Elementary consequence of the formal barrierValue, scaleDeriv and derivZeroPlus definitions together with positivity/monotonicity of the q-scale function. Used for the zero-barrier branch of Proposition 1 and Theorem 2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem barrierValue_zero_zero_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 := by
  sorry

end AvramDividend.Classical
