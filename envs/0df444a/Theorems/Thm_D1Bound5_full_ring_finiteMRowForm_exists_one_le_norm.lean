-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finiteMRowForm_exists_one_le_norm
-- name    : D1Bound5.full_ring_finiteMRowForm_exists_one_le_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:15:21.102574+00:00
-- url     : https://prove2.me/theorems/ab4a3fe7-b53c-4591-8ddf-6bc2de220a4c
-- title:
--   Full ring finite MRow Form exists one le norm
-- statement:
--   An actual integral M row is nonzero because the proved divided matrix determinant is nonzero. Arbitrary signed root products are allowed, provided the terminal root is nonzero.
-- source:
--   D1Bound5/FiniteMIntegralRows.lean, lines 41-76, SHA-256 6a41917e374548988e846d67ca045f1fa413585ce5c57ae666d21b73fb0a0713. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.full_ring_finiteMRowForm_exists_one_le_norm
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b s c z rA rB rS : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) (hz : z ≠ 0) :
    ∃ i : Fin 4, 1 ≤ ‖finiteMRowForm (phi (a : K)) (phi (b : K)) (phi (s : K))
      (phi (c : K)) (phi (z : K)) (phi (rA : K)) (phi (rB : K)) (phi (rS : K)) i‖ := by sorry

end D1Bound5
end
