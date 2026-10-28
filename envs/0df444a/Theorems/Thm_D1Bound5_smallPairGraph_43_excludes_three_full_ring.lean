-- Prove2me | Theorems.Thm_D1Bound5_smallPairGraph_43_excludes_three_full_ring
-- name    : D1Bound5.smallPairGraph_43_excludes_three_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:43:59.498246+00:00
-- url     : https://prove2.me/theorems/855041c2-a8bd-40ce-a56f-8a68a1adadc3
-- title:
--   Small Pair Graph 43 excludes three full ring
-- statement:
--   Complete large-extension triangle exclusion for pair-table row 43.
-- source:
--   D1Bound5/SmallPairGraphFullRing43.lean, lines 9-29, SHA-256 5a6048fd57512696fd0a51066324d14d4e210362329e3931bc4126137b0b4efa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Order.Ring.Abs
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
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_001

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.smallPairGraph_43_excludes_three_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 3 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 1 3)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_43 smallPairB_43 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_43) (hneB : ∀ i, t i ≠ smallPairB_43) : False := by sorry

end D1Bound5
end
