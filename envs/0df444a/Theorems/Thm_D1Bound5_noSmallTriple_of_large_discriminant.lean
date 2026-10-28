-- Prove2me | Theorems.Thm_D1Bound5_noSmallTriple_of_large_discriminant
-- name    : D1Bound5.noSmallTriple_of_large_discriminant
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:27:11.02002+00:00
-- url     : https://prove2.me/theorems/be8706f5-f372-423e-b7fd-204dbb264599
-- title:
--   No Small Triple of large discriminant
-- statement:
--   Above discriminant 32, even three small entries are impossible.
-- source:
--   D1Bound5/SmallTripleClassification.lean, lines 12-56, SHA-256 29c06a840b00bae4fa8a3417f349d7002808f0195fa16482f0c5528783af6485. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.noSmallTriple_of_large_discriminant {tau nu : ℤ}
    (hlarge : 32 < discriminant tau nu) : ∀ t : Fin 3 → QuadInt tau nu,
      IsD1Tuple t → (∀ i, (t i).norm ≤ 8) → False := by sorry





end D1Bound5
end
