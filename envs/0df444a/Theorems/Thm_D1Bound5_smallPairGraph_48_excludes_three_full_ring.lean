-- Prove2me | Theorems.Thm_D1Bound5_smallPairGraph_48_excludes_three_full_ring
-- name    : D1Bound5.smallPairGraph_48_excludes_three_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:08.902753+00:00
-- url     : https://prove2.me/theorems/92161d64-5ed4-4051-b68f-98ff9c58ffcf
-- title:
--   Small Pair Graph 48 excludes three full ring
-- statement:
--   Complete large-extension triangle exclusion for pair-table row 48.
-- source:
--   D1Bound5/SmallPairGraphFullRing48.lean, lines 9-29, SHA-256 3e654170956a9bb537a78e60777dde8c6176b1952eab85e0ce8d98af4d9b3c39. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs48_Definitions_001

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.smallPairGraph_48_excludes_three_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 8 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 1 8)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_48 smallPairB_48 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_48) (hneB : ∀ i, t i ≠ smallPairB_48) : False := by sorry

end D1Bound5
end
