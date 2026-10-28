-- Prove2me | Theorems.Thm_D1Bound5_smallPairGraph_13_excludes_three_full_ring
-- name    : D1Bound5.smallPairGraph_13_excludes_three_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:36:05.989832+00:00
-- url     : https://prove2.me/theorems/d3bf6a06-ee55-4999-9372-d5874303080e
-- title:
--   Small Pair Graph 13 excludes three full ring
-- statement:
--   Complete large-extension triangle exclusion for pair-table row 13.
-- source:
--   D1Bound5/SmallPairGraphFullRing13.lean, lines 9-29, SHA-256 918f6ef9c79f671102708c2c8925519e18303eedc6723683909af1c38c9eb959. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphData13_Definitions_001

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.smallPairGraph_13_excludes_three_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 2 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 0 2)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_13 smallPairB_13 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_13) (hneB : ∀ i, t i ≠ smallPairB_13) : False := by sorry

end D1Bound5
end
