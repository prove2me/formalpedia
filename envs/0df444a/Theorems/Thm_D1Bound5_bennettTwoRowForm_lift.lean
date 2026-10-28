-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoRowForm_lift
-- name    : D1Bound5.bennettTwoRowForm_lift
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:23:34.876646+00:00
-- url     : https://prove2.me/theorems/a5d11ef9-98a0-47d6-8a6b-ae9ad55aba6b
-- title:
--   Bennett Two Row Form lift
-- statement:
--   The selected row is the image of an explicitly constructed ring element. This uses the proved column divisibilities at every positive order, including k=1.
-- source:
--   D1Bound5/BennettIntegralRowSelection.lean, lines 42-61, SHA-256 9c3c5f22bb6cb848bdf27168f61bbb1b8947f740ff7556d2698f7ee50542b384. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.bennettTwoRowForm_lift
    {R F : Type*} [CommRing R] [Field F] [CharZero F]
    (f : R →+* F) (a b c z sA sB : R)
    (ha : f a ≠ 0) (hb : f b ≠ 0) (hab : f a ≠ f b)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ∃ L : R, f L = bennettTwoRowForm (f a) (f b) (f c) (f z) (f sA) (f sB) k i := by sorry



end D1Bound5
end
