-- Prove2me | Theorems.Thm_D1Bound5_weightedCS_four_row
-- name    : D1Bound5.weightedCS_four_row
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:22:39.527995+00:00
-- url     : https://prove2.me/theorems/6b399f31-f49c-44d6-8cde-e2a47ce8daa8
-- title:
--   Weighted CS four row
-- statement:
--   Weighted finite Cauchy--Schwarz without square roots or positivity of x.
-- source:
--   D1Bound5/WeightedSchur.lean, lines 10-23, SHA-256 0740899bda0b97ce5440dc1a326c7e0aa61aa178424db90f7d296c6acdfafdf8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5


theorem _root_.D1Bound5.weightedCS_four_row (b w x : Fin 4 → ℝ)
    (hb : ∀ j, 0 ≤ b j) (hw : ∀ j, 0 < w j) :
    (∑ j, b j * x j)^2 ≤
      (∑ j, b j * w j) * (∑ j, b j * (x j)^2 / w j) := by sorry

end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5





end D1Bound5
end
