-- Prove2me | Theorems.Thm_D1Bound5_smallPairGraph_47_excludes_three_full_ring
-- name    : D1Bound5.smallPairGraph_47_excludes_three_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:35:42.590827+00:00
-- url     : https://prove2.me/theorems/0a0af260-748f-4cf7-8210-5f25e8a632ea
-- title:
--   Small Pair Graph 47 excludes three full ring
-- statement:
--   Complete large-extension triangle exclusion for pair-table row 47.
-- source:
--   D1Bound5/SmallPairGraphFullRing47.lean, lines 9-29, SHA-256 46e821407ecb90ad2bf4a0ebadb208abe3c6e73ea45cc788a8716f2d61d0fdd5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs47_Definitions_001

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.smallPairGraph_47_excludes_three_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 6 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 1 6)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_47 smallPairB_47 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_47) (hneB : ∀ i, t i ≠ smallPairB_47) : False := by sorry

end D1Bound5
end
