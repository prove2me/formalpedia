-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_shift_bounds_of_nonpositive
-- name    : AvramDividend.Classical.scaleFunction_shift_bounds_of_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T11:30:06.676976+00:00
-- url     : https://prove2.me/theorems/ff973782-83b8-4891-9807-9db2d38587eb
-- title:
--   A scale function decreases under nonpositive shifts
-- statement:
--   If x is nonnegative and y is a nonpositive jump, then the q-scale function at x+y lies between 0 and W(x). When x+y is negative the scale function is zero by definition. Otherwise both x+y and x are in [0,infinity), and monotonicity gives W(x+y) <= W(x). This is the far-jump bound used in generator-integrability estimates.
-- source:
--   Direct consequence of the defining support, nonnegativity and monotonicity clauses of IsScaleFunction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_shift_bounds_of_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x y : ℝ) (hx : 0 ≤ x) (hy : y ≤ 0) :
    0 ≤ W (x + y) ∧ W (x + y) ≤ W x := by sorry
