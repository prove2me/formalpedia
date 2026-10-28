-- Prove2me | Theorems.Thm_D1Bound5_full_ring_bennettTwoRowForm_exists_one_le_norm
-- name    : D1Bound5.full_ring_bennettTwoRowForm_exists_one_le_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:22:51.629657+00:00
-- url     : https://prove2.me/theorems/1c00ab45-1bb8-4587-a55a-7aeb3fa6f4d9
-- title:
--   Full ring bennett Two Row Form exists one le norm
-- statement:
--   In the full ring of integers of an imaginary quadratic field, an actual Bennett row has modulus at least one. The determinant and integrality are both derived from the constructed entries. The root arguments can be any signed integral lifts obtained from the tuple.
-- source:
--   D1Bound5/BennettIntegralRowSelection.lean, lines 63-97, SHA-256 9c3c5f22bb6cb848bdf27168f61bbb1b8947f740ff7556d2698f7ee50542b384. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.full_ring_bennettTwoRowForm_exists_one_le_norm
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b c z sA sB : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hz : z ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    ∃ i : Fin 3, 1 ≤ ‖bennettTwoRowForm (phi (a : K)) (phi (b : K))
      (phi (c : K)) (phi (z : K)) (phi (sA : K)) (phi (sB : K)) k i‖ := by sorry

end D1Bound5
end
