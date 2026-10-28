-- Prove2me | Theorems.Thm_D1Bound5_finite_choose_two
-- name    : D1Bound5.finite_choose_two
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:11.457779+00:00
-- url     : https://prove2.me/theorems/eb89aa24-ee03-420b-942e-322f2f98587f
-- title:
--   Finite choose two
-- statement:
--   The second generalized binomial coefficient, derived from the actual choose multiplication identity.
-- source:
--   D1Bound5/FiniteN2BennettIdentity.lean, lines 10-16, SHA-256 fcacc869d2713078cd69f64d108df5778a46eb1540584038908ffb1d2b408ba4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]


theorem _root_.D1Bound5.finite_choose_two (r : F) : Ring.choose r 2 = r*(r-1)/2 := by sorry



end D1Bound5
end
