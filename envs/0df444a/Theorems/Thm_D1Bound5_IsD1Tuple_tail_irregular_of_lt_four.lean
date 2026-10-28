-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_tail_irregular_of_lt_four
-- name    : D1Bound5.IsD1Tuple.tail_irregular_of_lt_four
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:15:26.851211+00:00
-- url     : https://prove2.me/theorems/efaab116-6747-40b2-814e-285175e6e953
-- title:
--   Is D1Tuple — tail irregular of lt four
-- statement:
--   The finite C<4 case of the tail lemma, transported through the proved full integer-ring equivalence. This includes every imaginary quadratic field.
-- source:
--   D1Bound5/TailIrregular.lean, lines 10-63, SHA-256 98aee920c9839181f5a78733c62a31450435bbb6574947c82f20fe99ca99dcdd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_Regular_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.IsD1Tuple.tail_irregular_of_lt_four
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hB : 3 ≤ ‖phi (t 1 : K)‖) (hC : ‖phi (t 2 : K)‖ < 4) :
    regularDefect (t 1) (t 2) (t 3) ≠ 0 := by sorry



end D1Bound5
end
