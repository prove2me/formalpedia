-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_properCommonExtension_first_two
-- name    : D1Bound5.IsD1Tuple.properCommonExtension_first_two
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:52:18.869706+00:00
-- url     : https://prove2.me/theorems/042521b3-ec04-45ad-b5d0-1cb64e3a6f2b
-- title:
--   Is D1Tuple — proper Common Extension first two
-- statement:
--   All entries following the first two are proper common extensions.
-- source:
--   D1Bound5/TwoSmallSextuple.lean, lines 8-25, SHA-256 9345634335e2eff34f0f86c463393f8a5fbec088163026119ac596585f6b6500. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
open scoped NumberField Classical
open Module

namespace D1Bound5


theorem _root_.D1Bound5.IsD1Tuple.properCommonExtension_first_two
    {R : Type*} [CommRing R] [DecidableEq R]
    (t : Fin 6 → R) (ht : IsD1Tuple t) (j : Fin 6) (hj : 2 ≤ j) :
    ProperCommonExtension {t 0,t 1} (t j) := by sorry



end D1Bound5
end
