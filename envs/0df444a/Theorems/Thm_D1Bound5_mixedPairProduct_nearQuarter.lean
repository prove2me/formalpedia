-- Prove2me | Theorems.Thm_D1Bound5_mixedPairProduct_nearQuarter
-- name    : D1Bound5.mixedPairProduct_nearQuarter
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:04.865993+00:00
-- url     : https://prove2.me/theorems/2c25e204-af2f-42e2-80a7-868aee83f965
-- title:
--   Mixed Pair Product near Quarter
-- statement:
--   A product of a first-row and a later-row normalized root entry lies within 7/192 of one quarter. The two error radii are different.
-- source:
--   D1Bound5/MixedFourDetBound.lean, lines 8-45, SHA-256 863a07b764253ce476290edc497efddecf3c39545921323e93756d8912d3da78. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Matrix

namespace D1Bound5


theorem _root_.D1Bound5.mixedPairProduct_nearQuarter (x y : ℂ)
    (hx : ‖x - (1/2 : ℂ)‖ < (1/18 : ℝ))
    (hy : ‖y - (1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖x*y - (1/4 : ℂ)‖ < (7/192 : ℝ) := by sorry





end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5



end D1Bound5
end
