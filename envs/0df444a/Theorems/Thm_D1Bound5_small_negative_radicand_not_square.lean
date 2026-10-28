-- Prove2me | Theorems.Thm_D1Bound5_small_negative_radicand_not_square
-- name    : D1Bound5.small_negative_radicand_not_square
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:45:14.883423+00:00
-- url     : https://prove2.me/theorems/46934374-4562-49b8-be4f-8c5a248a90ed
-- title:
--   Small negative radicand not square
-- statement:
--   The two negative rational radicands are excluded uniformly beyond Δ=32.
-- source:
--   D1Bound5/SmallPairLargeDiscriminant.lean, lines 20-31, SHA-256 c69437fd6732a6665be073a5675405812d333a1b31dbbd565010be6a462d9850. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
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

section
namespace D1Bound5
open QuadInt






theorem _root_.D1Bound5.small_negative_radicand_not_square {tau nu m : ℤ}
    (hlarge : 32 < discriminant tau nu) (hm : m = -1 ∨ m = -3) :
    ¬ ∃ r : QuadInt tau nu, r*r = (m : QuadInt tau nu) := by sorry





end D1Bound5
end
