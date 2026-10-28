-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_crossBlock_growth
-- name    : D1Bound5.IsD1Tuple.crossBlock_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:08:19.639972+00:00
-- url     : https://prove2.me/theorems/15edd0ef-f3f0-4bab-8e3c-9d5941c57192
-- title:
--   Is D1Tuple — cross Block growth
-- statement:
--   The manuscript's cross-block inequality for any two disjoint triples inside an actual D(1)-tuple. Only the stated separate order and initial size hypotheses remain.
-- source:
--   D1Bound5/CrossBlockTuple.lean, lines 159-178, SHA-256 4f7736bd25878caf4f646f90a08781588133d8497db784873e94a7e8e819b915. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_IsD1Tuple

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5










theorem _root_.D1Bound5.IsD1Tuple.crossBlock_growth
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {n : ℕ} (t : Fin n → 𝓞 K) (ht : IsD1Tuple t)
    (p q : Fin 3 ↪ Fin n) (hpq : ∀ i j, p i ≠ q j)
    (hmonA : Monotone (fun i => ‖phi (t (p i) : K)‖))
    (hmonB : Monotone (fun i => ‖phi (t (q i) : K)‖))
    (hlarge : 9 ≤ ‖phi (t (p 0) : K)‖*‖phi (t (q 0) : K)‖) :
    (‖phi (t (p 0) : K)‖*‖phi (t (q 0) : K)‖)^3*
        (‖phi (t (p 1) : K)‖*‖phi (t (q 1) : K)‖)/7 <
      ‖phi (t (p 2) : K)‖*‖phi (t (q 2) : K)‖ := by sorry

end D1Bound5
end
