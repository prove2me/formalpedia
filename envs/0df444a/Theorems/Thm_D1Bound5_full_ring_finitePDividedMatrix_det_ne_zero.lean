-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finitePDividedMatrix_det_ne_zero
-- name    : D1Bound5.full_ring_finitePDividedMatrix_det_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:02.747042+00:00
-- url     : https://prove2.me/theorems/af99f172-e138-4209-bc02-6f937770b5b2
-- title:
--   Full ring finite PDivided Matrix det ne zero
-- statement:
--   Auxiliary result `full_ring_finitePDividedMatrix_det_ne_zero` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePIntegralRows.lean, lines 100-124, SHA-256 f4ae4543e8d296d5524652a8ec1de382e8c69fd4002555ade9ad3f247eeee37c. Project: https://github.com/tomislav-math/d1-bound5-lean

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















theorem _root_.D1Bound5.full_ring_finitePDividedMatrix_det_ne_zero
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ) (a b s c : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖)
    (hBS : ‖phi (b : K)‖ ≤ ‖phi (s : K)‖)
    (hC : 200*‖phi (s : K)‖ ≤ ‖phi (c : K)‖) :
    (finitePDividedMatrix (phi (a : K)) (phi (b : K)) (phi (s : K)) (phi (c : K))).det ≠ 0 := by sorry







end D1Bound5
end
