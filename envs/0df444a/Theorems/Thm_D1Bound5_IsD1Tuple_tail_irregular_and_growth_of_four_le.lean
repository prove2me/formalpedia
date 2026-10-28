-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_tail_irregular_and_growth_of_four_le
-- name    : D1Bound5.IsD1Tuple.tail_irregular_and_growth_of_four_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:15:29.359018+00:00
-- url     : https://prove2.me/theorems/0b842e8c-3aa7-431f-9fce-d24a75df5636
-- title:
--   Is D1Tuple — tail irregular and growth of four le
-- statement:
--   The large-C tail lemma and its growth consequence for an actual ordered D(1) quadruple. Monotonicity allows equal moduli.
-- source:
--   D1Bound5/TailAnalyticMain.lean, lines 181-204, SHA-256 ecaba9e1e964c7e6c51088002aaaf592031aa2393ee6eb52d94273cfda86b389. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_Regular_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5







theorem _root_.D1Bound5.IsD1Tuple.tail_irregular_and_growth_of_four_le
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hB : 3 ≤ ‖phi (t 1 : K)‖) (hC : 4 ≤ ‖phi (t 2 : K)‖) :
    regularDefect (t 1) (t 2) (t 3) ≠ 0 ∧
      2*‖phi (t 1 : K)‖*‖phi (t 2 : K)‖ < ‖phi (t 3 : K)‖ := by sorry

end D1Bound5
end
