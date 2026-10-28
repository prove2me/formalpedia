-- Prove2me | Theorems.Thm_D1Bound5_finiteN3_choose_two
-- name    : D1Bound5.finiteN3_choose_two
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:16.676995+00:00
-- url     : https://prove2.me/theorems/c5d04da9-6d7e-4514-9861-f963e92d052b
-- title:
--   Finite N3 choose two
-- statement:
--   The second generalized binomial coefficient, derived from the actual choose multiplication identity.
-- source:
--   D1Bound5/FiniteN3BennettIdentity.lean, lines 10-16, SHA-256 9148242701768b71c2b658d39b171d28a071514528febee5c27aae9756a4480e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.finiteN3_choose_two (r : F) : Ring.choose r 2 = r*(r-1)/2 := by sorry





end D1Bound5
end
