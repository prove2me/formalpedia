-- Prove2me | Theorems.Thm_D1Bound5_crossBlock_growth_of_scaled_determinant
-- name    : D1Bound5.crossBlock_growth_of_scaled_determinant
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:27:33.46911+00:00
-- url     : https://prove2.me/theorems/82b7bb61-3c0a-4ab5-8272-6f40c16924ae
-- title:
--   Cross Block growth of scaled determinant
-- statement:
--   The final real arithmetic of the cross-block argument, in a form that does not use square roots or division by a possibly zero determinant.
-- source:
--   D1Bound5/CrossBlockGrowth.lean, lines 98-118, SHA-256 3777e46d483287a817b131071ac51c08d504f0feca7cb831dcc041f533f01f1c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5










theorem _root_.D1Bound5.crossBlock_growth_of_scaled_determinant
    (W0 W1 W2 d : ℝ) (hW0 : 9 ≤ W0) (hW1 : 9 ≤ W1) (hW2 : 9 ≤ W2)
    (hd : 0 ≤ d) (hlower : (W0*W1*W2)^3 ≤ d^2)
    (hupper : d < (5/2 : ℝ)*W2^2*W1) :
    W0^3*W1/7 < W2 := by sorry

end D1Bound5
end
