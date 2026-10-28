-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_three_small_fifth_large
-- name    : D1Bound5.IsD1Tuple.three_small_fifth_large
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:50:42.477068+00:00
-- url     : https://prove2.me/theorems/169003a4-694f-49e3-9d7c-f975fceb740f
-- title:
--   Is D1Tuple — three small fifth large
-- statement:
--   An ordered actual sextuple with three small initial entries must have fifth modulus greater than 10^40. Its fourth modulus is either less than 85 or also greater than 10^40. This follows from complete bounded-extension uniqueness, without any bound on the final tuple entry.
-- source:
--   D1Bound5/ThreeSmallSextuple.lean, lines 38-86, SHA-256 92e6b66ee26fa4969f4ba389855443d9744795188e2160b190dc72e04a9ee52f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
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
import Mathlib.Data.List.Range
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






theorem _root_.D1Bound5.IsD1Tuple.three_small_fifth_large
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 6 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hsmall : ‖phi (t 2 : K)‖ < 3) :
    (10 : ℝ)^40 < ‖phi (t 4 : K)‖ ∧
      (‖phi (t 3 : K)‖ < 85 ∨ (10 : ℝ)^40 < ‖phi (t 3 : K)‖) := by sorry

end D1Bound5
end
