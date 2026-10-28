-- Prove2me | Theorems.Thm_D1Bound5_smallTripleExtension_10_complete_full_ring
-- name    : D1Bound5.smallTripleExtension_10_complete_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:48:32.864578+00:00
-- url     : https://prove2.me/theorems/fea405b6-026f-492c-a9cf-caebfa88adb2
-- title:
--   Small Triple Extension 10 complete full ring
-- statement:
--   Complete radius-10^40 extension list for manuscript row 10.
-- source:
--   D1Bound5/SmallTripleExtensions.lean, lines 307-337, SHA-256 4012985a91d9c7e7f8ef52a242c3eb2b671af1516c44413e2d52d177518230c5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallTripleExtensionData10_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt




















theorem _root_.D1Bound5.smallTripleExtension_10_complete_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 2 ≃+* 𝓞 K) (z : QuadInt 1 2)
    (hpair : PairExtension smallTripleAnchorA_10 smallTripleAnchorB_10 z)
    (hthird : ∃ r, r*r = smallTripleAnchorC_10*z+1)
    (hz : z ≠ 0) (ha : z ≠ smallTripleAnchorA_10)
    (hb : z ≠ smallTripleAnchorB_10) (hc : z ≠ smallTripleAnchorC_10)
    (hNz : z.norm ≤ 10^80) :
    z ∈ smallTripleAllowed_10 := by sorry

end D1Bound5
end
