-- Prove2me | Theorems.Thm_D1Bound5_finiteN2_bennett_identity
-- name    : D1Bound5.finiteN2_bennett_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:34:47.40855+00:00
-- url     : https://prove2.me/theorems/ba8935a3-7244-4559-a7f7-6703a94a3d91
-- title:
--   Finite N2 bennett identity
-- statement:
--   Exact identification of the N2 integer polynomials with the actual ordinary Bennett matrix at k=2. The row factors are precisely 2(x-y),2x,2y; no residue identity is supplied as a hypothesis.
-- source:
--   D1Bound5/FiniteN2BennettIdentity.lean, lines 19-54, SHA-256 fcacc869d2713078cd69f64d108df5778a46eb1540584038908ffb1d2b408ba4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



set_option maxHeartbeats 2000000 in

theorem _root_.D1Bound5.finiteN2_bennett_identity (x y c : F)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (i j : Fin 3) :
    bennettTwoClearedEntry x y c 2 i j =
      2 * finiteN2RowFactor x y i * finiteN2Matrix x y c i j := by sorry

end D1Bound5
end
