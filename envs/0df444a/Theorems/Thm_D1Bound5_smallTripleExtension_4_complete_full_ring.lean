-- Prove2me | Theorems.Thm_D1Bound5_smallTripleExtension_4_complete_full_ring
-- name    : D1Bound5.smallTripleExtension_4_complete_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:23:41.865162+00:00
-- url     : https://prove2.me/theorems/4003bc45-c1fe-4087-b566-facb9e52c1d6
-- title:
--   Small Triple Extension 4 complete full ring
-- statement:
--   Complete radius-10^40 extension list for manuscript row 4.
-- source:
--   D1Bound5/SmallTripleExtensions.lean, lines 115-145, SHA-256 4012985a91d9c7e7f8ef52a242c3eb2b671af1516c44413e2d52d177518230c5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData4_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt








theorem _root_.D1Bound5.smallTripleExtension_4_complete_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 1 ≃+* 𝓞 K) (z : QuadInt 0 1)
    (hpair : PairExtension smallTripleAnchorA_4 smallTripleAnchorB_4 z)
    (hthird : ∃ r, r*r = smallTripleAnchorC_4*z+1)
    (hz : z ≠ 0) (ha : z ≠ smallTripleAnchorA_4)
    (hb : z ≠ smallTripleAnchorB_4) (hc : z ≠ smallTripleAnchorC_4)
    (hNz : z.norm ≤ 10^80) :
    z ∈ smallTripleAllowed_4 := by sorry













end D1Bound5
end
