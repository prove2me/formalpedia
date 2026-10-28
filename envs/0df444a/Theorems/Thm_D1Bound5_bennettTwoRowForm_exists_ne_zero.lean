-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoRowForm_exists_ne_zero
-- name    : D1Bound5.bennettTwoRowForm_exists_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:23:38.922071+00:00
-- url     : https://prove2.me/theorems/9db2f10c-e378-4db5-a856-c6f5935321f6
-- title:
--   Bennett Two Row Form exists ne zero
-- statement:
--   The constructed determinant supplies an actual nonzero row whenever the terminal root is nonzero. No nonsingularity hypothesis is supplied.
-- source:
--   D1Bound5/BennettIntegralRowSelection.lean, lines 18-40, SHA-256 9c3c5f22bb6cb848bdf27168f61bbb1b8947f740ff7556d2698f7ee50542b384. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettIntegralRowSelection_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.bennettTwoRowForm_exists_ne_zero
    {F : Type*} [Field F] [CharZero F]
    (a b c z sA sB : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hz : z ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    ∃ i : Fin 3, bennettTwoRowForm a b c z sA sB k i ≠ 0 := by sorry





end D1Bound5
end
