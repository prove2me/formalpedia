-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finitePDetFactor_ne_zero
-- name    : D1Bound5.full_ring_finitePDetFactor_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:44:26.219411+00:00
-- url     : https://prove2.me/theorems/5c6e34a4-f10d-41bd-9386-69ad7038ab67
-- title:
--   Full ring finite PDet Factor ne zero
-- statement:
--   Actual integral arithmetic rules out a zero determinant factor. A nonzero leading factor is an algebraic integer of norm at least one; a zero leading factor is excluded by the exact identity above.
-- source:
--   D1Bound5/FinitePIntegralRows.lean, lines 45-98, SHA-256 f4ae4543e8d296d5524652a8ec1de382e8c69fd4002555ade9ad3f247eeee37c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5














theorem _root_.D1Bound5.full_ring_finitePDetFactor_ne_zero
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ) (a b s c : 𝓞 K)
    (hs : s ≠ 0) (hab : a ≠ b)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖)
    (hBS : ‖phi (b : K)‖ ≤ ‖phi (s : K)‖)
    (hC : 200*‖phi (s : K)‖ ≤ ‖phi (c : K)‖) :
    finitePDetFactor (phi (a : K)) (phi (b : K)) (phi (s : K)) (phi (c : K)) ≠ 0 := by sorry









end D1Bound5
end
