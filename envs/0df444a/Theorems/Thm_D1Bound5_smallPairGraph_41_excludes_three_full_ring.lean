-- Prove2me | Theorems.Thm_D1Bound5_smallPairGraph_41_excludes_three_full_ring
-- name    : D1Bound5.smallPairGraph_41_excludes_three_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:12.527809+00:00
-- url     : https://prove2.me/theorems/3e59cd6f-299b-45d0-a074-f3da094f6e58
-- title:
--   Small Pair Graph 41 excludes three full ring
-- statement:
--   Complete large-extension triangle exclusion for pair-table row 41.
-- source:
--   D1Bound5/SmallPairGraphFullRing41.lean, lines 9-29, SHA-256 7b7f404af6ac1ce0d0ee2be2b87bc14be459cd19e6fc1ff3b94c1c7bedac6921. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphData41_Definitions_001

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.smallPairGraph_41_excludes_three_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 2 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 1 2)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_41 smallPairB_41 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_41) (hneB : ∀ i, t i ≠ smallPairB_41) : False := by sorry

end D1Bound5
end
