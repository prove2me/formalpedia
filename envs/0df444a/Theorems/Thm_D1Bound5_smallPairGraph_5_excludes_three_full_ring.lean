-- Prove2me | Theorems.Thm_D1Bound5_smallPairGraph_5_excludes_three_full_ring
-- name    : D1Bound5.smallPairGraph_5_excludes_three_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:33:50.060449+00:00
-- url     : https://prove2.me/theorems/b46e39e8-5adf-4964-828c-96bcc4a1a0e6
-- title:
--   Small Pair Graph 5 excludes three full ring
-- statement:
--   Complete large-extension triangle exclusion for pair-table row 5.
-- source:
--   D1Bound5/SmallPairGraphFullRingGroupPilot235.lean, lines 55-75, SHA-256 29aec01e8b252d49891b82d38b45df918e32fe132da3def30ab69a0b139b7a02. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs5_Definitions_001

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt






theorem _root_.D1Bound5.smallPairGraph_5_excludes_three_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 1 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 0 1)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_5 smallPairB_5 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_5) (hneB : ∀ i, t i ≠ smallPairB_5) : False := by sorry

end D1Bound5
end
