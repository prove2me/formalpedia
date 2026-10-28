-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_two_small_fifth_large
-- name    : D1Bound5.IsD1Tuple.two_small_fifth_large
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:50:45.005343+00:00
-- url     : https://prove2.me/theorems/2ee90108-c233-44bd-b8a2-6f7350c24667
-- title:
--   Is D1Tuple — two small fifth large
-- statement:
--   In an ordered sextuple with exactly two small initial entries and a nondegenerate anchor product, the fifth modulus exceeds 10^550.
-- source:
--   D1Bound5/TwoSmallSextuple.lean, lines 27-74, SHA-256 9345634335e2eff34f0f86c463393f8a5fbec088163026119ac596585f6b6500. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple

section
open scoped NumberField Classical
open Module

namespace D1Bound5




theorem _root_.D1Bound5.IsD1Tuple.two_small_fifth_large
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 6 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hsmall : ‖phi (t 1 : K)‖ < 3)
    (hlarge : 3 ≤ ‖phi (t 2 : K)‖)
    (hnondeg : t 0*t 1+1 ≠ 0) :
    (10 : ℝ)^550 < ‖phi (t 4 : K)‖ := by sorry

end D1Bound5
end
