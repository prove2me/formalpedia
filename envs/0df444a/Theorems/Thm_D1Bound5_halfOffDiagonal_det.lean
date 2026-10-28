-- Prove2me | Theorems.Thm_D1Bound5_halfOffDiagonal_det
-- name    : D1Bound5.halfOffDiagonal_det
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:30:18.433075+00:00
-- url     : https://prove2.me/theorems/e21e1b00-dc41-4238-8eed-526cfefb8524
-- title:
--   Half Off Diagonal det
-- statement:
--   Exact reference determinant, obtained from the rank-one determinant lemma rather than a computer expansion of twenty-four permutation terms.
-- source:
--   D1Bound5/ReferenceMatrixSpectral.lean, lines 41-60, SHA-256 a9d2534dbab31dc06c160d4476f3546ac57b74623f0a03cba8eaeb8e7e822001. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5













theorem _root_.D1Bound5.halfOffDiagonal_det : halfOffDiagonal.det = (-3/16 : ℂ) := by sorry





end D1Bound5
end
