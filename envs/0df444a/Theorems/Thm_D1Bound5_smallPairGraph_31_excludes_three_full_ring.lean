-- Prove2me | Theorems.Thm_D1Bound5_smallPairGraph_31_excludes_three_full_ring
-- name    : D1Bound5.smallPairGraph_31_excludes_three_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:38:29.592299+00:00
-- url     : https://prove2.me/theorems/756546f2-b55d-479c-ab1e-b030f803781d
-- title:
--   Small Pair Graph 31 excludes three full ring
-- statement:
--   Complete large-extension triangle exclusion for pair-table row 31.
-- source:
--   D1Bound5/SmallPairGraphFullRing31.lean, lines 9-29, SHA-256 f2399a021f157ff7333a9e86932463b7a2499f440e20e02a2e33786051ce286c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs31_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.smallPairGraph_31_excludes_three_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 5 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 0 5)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_31 smallPairB_31 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_31) (hneB : ∀ i, t i ≠ smallPairB_31) : False := by sorry

end D1Bound5
end
