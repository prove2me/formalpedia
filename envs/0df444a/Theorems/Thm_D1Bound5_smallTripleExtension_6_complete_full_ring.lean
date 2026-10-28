-- Prove2me | Theorems.Thm_D1Bound5_smallTripleExtension_6_complete_full_ring
-- name    : D1Bound5.smallTripleExtension_6_complete_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:23:28.673161+00:00
-- url     : https://prove2.me/theorems/ab983c1a-677a-4d6e-839f-7888511108c0
-- title:
--   Small Triple Extension 6 complete full ring
-- statement:
--   Complete radius-10^40 extension list for manuscript row 6.
-- source:
--   D1Bound5/SmallTripleExtensions.lean, lines 179-209, SHA-256 4012985a91d9c7e7f8ef52a242c3eb2b671af1516c44413e2d52d177518230c5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData6_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt












theorem _root_.D1Bound5.smallTripleExtension_6_complete_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 1 ≃+* 𝓞 K) (z : QuadInt 1 1)
    (hpair : PairExtension smallTripleAnchorA_6 smallTripleAnchorB_6 z)
    (hthird : ∃ r, r*r = smallTripleAnchorC_6*z+1)
    (hz : z ≠ 0) (ha : z ≠ smallTripleAnchorA_6)
    (hb : z ≠ smallTripleAnchorB_6) (hc : z ≠ smallTripleAnchorC_6)
    (hNz : z.norm ≤ 10^80) :
    z ∈ smallTripleAllowed_6 := by sorry









end D1Bound5
end
