-- Prove2me | Theorems.Thm_D1Bound5_finiteN3_bennett_identity
-- name    : D1Bound5.finiteN3_bennett_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:25:41.896029+00:00
-- url     : https://prove2.me/theorems/348f406d-7b2c-425d-b489-032bd7ed14ea
-- title:
--   Finite N3 bennett identity
-- statement:
--   Exact identification of the N3 integer polynomials with the actual ordinary Bennett matrix at k=3. The row factors are precisely 4(x-y),4x,4y; no residue identity is supplied as a hypothesis.
-- source:
--   D1Bound5/FiniteN3BennettIdentity.lean, lines 25-61, SHA-256 9148242701768b71c2b658d39b171d28a071514528febee5c27aae9756a4480e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





set_option maxHeartbeats 4000000 in

theorem _root_.D1Bound5.finiteN3_bennett_identity (x y c : F)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (i j : Fin 3) :
    bennettTwoClearedEntry x y c 3 i j =
      4 * finiteN3RowFactor x y i * finiteN3Matrix x y c i j := by sorry

end D1Bound5
end
