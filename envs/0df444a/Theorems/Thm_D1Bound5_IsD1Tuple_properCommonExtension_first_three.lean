-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_properCommonExtension_first_three
-- name    : D1Bound5.IsD1Tuple.properCommonExtension_first_three
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:53:52.803209+00:00
-- url     : https://prove2.me/theorems/07782d14-ac75-43ac-9528-4b4f3ce89645
-- title:
--   Is D1Tuple — proper Common Extension first three
-- statement:
--   Every entry after the first three is a proper common extension of them. The statement does not impose any condition on mutation intermediates.
-- source:
--   D1Bound5/ThreeSmallSextuple.lean, lines 15-36, SHA-256 92e6b66ee26fa4969f4ba389855443d9744795188e2160b190dc72e04a9ee52f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
open scoped NumberField Classical
open Module

namespace D1Bound5




theorem _root_.D1Bound5.IsD1Tuple.properCommonExtension_first_three
    {R : Type*} [CommRing R] [DecidableEq R]
    (t : Fin 6 → R) (ht : IsD1Tuple t) (j : Fin 6) (hj : 3 ≤ j) :
    ProperCommonExtension {t 0,t 1,t 2} (t j) := by sorry



end D1Bound5
end
