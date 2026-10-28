-- Prove2me | Theorems.Thm_D1Bound5_finiteN3_choose_three
-- name    : D1Bound5.finiteN3_choose_three
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:18.916244+00:00
-- url     : https://prove2.me/theorems/57f4732a-a5d2-4f47-9e23-fb86f8c28a40
-- title:
--   Finite N3 choose three
-- statement:
--   Auxiliary result `finiteN3_choose_three` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteN3BennettIdentity.lean, lines 18-22, SHA-256 9148242701768b71c2b658d39b171d28a071514528febee5c27aae9756a4480e. Project: https://github.com/tomislav-math/d1-bound5-lean

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



theorem _root_.D1Bound5.finiteN3_choose_three (r : F) : Ring.choose r 3 = r*(r-1)*(r-2)/6 := by sorry



end D1Bound5
end
