-- Prove2me | Theorems.Thm_D1Bound5_finiteMRowForm_exists_ne_zero
-- name    : D1Bound5.finiteMRowForm_exists_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:26:05.605002+00:00
-- url     : https://prove2.me/theorems/7834487a-1e82-47d6-beb2-7ea8dd287f3e
-- title:
--   Finite MRow Form exists ne zero
-- statement:
--   Auxiliary result `finiteMRowForm_exists_ne_zero` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteMIntegralRows.lean, lines 23-39, SHA-256 6a41917e374548988e846d67ca045f1fa413585ce5c57ae666d21b73fb0a0713. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMIntegralRows_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5





theorem _root_.D1Bound5.finiteMRowForm_exists_ne_zero
    {F : Type*} [Field F] [CharZero F]
    (a b s c z rA rB rS : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) (hz : z ≠ 0) :
    ∃ i : Fin 4, finiteMRowForm a b s c z rA rB rS i ≠ 0 := by sorry



end D1Bound5
end
