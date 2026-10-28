-- Prove2me | Theorems.Thm_D1Bound5_full_small_pair_model_allowed
-- name    : D1Bound5.full_small_pair_model_allowed
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:12:12.956564+00:00
-- url     : https://prove2.me/theorems/89706ee0-858c-42e0-a69e-e320f98c8850
-- title:
--   Full small pair model allowed
-- statement:
--   Maximality excludes the five extraneous coordinate orders in the finite rectangle. It is used only here, after complete finite-order classification.
-- source:
--   D1Bound5/SmallPairClassification.lean, lines 16-50, SHA-256 a32a3e7b2d5dfed4754fd2fe6af26c9e86156fe171110d66d6c2f3d17661c981. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt




theorem _root_.D1Bound5.full_small_pair_model_allowed
    {K : Type*} [Field K] [NumberField K]
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K)
    (htau : tau = 0 ∨ tau = 1) (hd : 0 < discriminant tau nu)
    (hlo : 1 ≤ nu) (hhi : nu ≤ 8) : (tau,nu) ∈ smallPairModels := by sorry



end D1Bound5
end
