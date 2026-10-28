-- Prove2me | Theorems.Thm_D1Bound5_full_ring_crossBlock_growth
-- name    : D1Bound5.full_ring_crossBlock_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:27:33.004389+00:00
-- url     : https://prove2.me/theorems/31641fac-f5dd-461b-9a39-2d446555b255
-- title:
--   Full ring cross Block growth
-- statement:
--   The complete cross-block growth lemma for the full integer ring of an arbitrary imaginary quadratic field.
-- source:
--   D1Bound5/CrossBlockTuple.lean, lines 141-157, SHA-256 4f7736bd25878caf4f646f90a08781588133d8497db784873e94a7e8e819b915. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5








theorem _root_.D1Bound5.full_ring_crossBlock_growth
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b : Fin 3 → 𝓞 K) (M : Fin 3 → Fin 3 → 𝓞 K)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hroot : ∀ i j, (M i j)^2 = a i*b j+1)
    (hmonA : Monotone (fun i => ‖phi (a i : K)‖))
    (hmonB : Monotone (fun i => ‖phi (b i : K)‖))
    (hlarge : 9 ≤ ‖phi (a 0 : K)‖*‖phi (b 0 : K)‖) :
    (‖phi (a 0 : K)‖*‖phi (b 0 : K)‖)^3*
        (‖phi (a 1 : K)‖*‖phi (b 1 : K)‖)/7 <
      ‖phi (a 2 : K)‖*‖phi (b 2 : K)‖ := by sorry



end D1Bound5
end
