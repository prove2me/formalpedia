-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoNodes_injective
-- name    : D1Bound5.bennettTwoNodes_injective
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:22:26.003232+00:00
-- url     : https://prove2.me/theorems/0a348984-8ee9-47af-af31-37500f116a78
-- title:
--   Bennett Two Nodes injective
-- statement:
--   Auxiliary result `bennettTwoNodes_injective` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/BennettTwoIntegralMatrix.lean, lines 9-13, SHA-256 136894d1b4f549edd11ad783443c9dfcdff9dc56c2e0bd789e83020f9f2279d2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

theorem _root_.D1Bound5.bennettTwoNodes_injective (a b : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Injective (bennettTwoNodes a b) := by sorry





end D1Bound5
end
