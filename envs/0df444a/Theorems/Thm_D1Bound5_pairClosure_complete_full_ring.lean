-- Prove2me | Theorems.Thm_D1Bound5_pairClosure_complete_full_ring
-- name    : D1Bound5.pairClosure_complete_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:34:46.313276+00:00
-- url     : https://prove2.me/theorems/9204df70-fd74-4ebc-9116-0707afbbb6b1
-- title:
--   Pair Closure complete full ring
-- statement:
--   Norm descent and algebraic reversibility turn two finite checks into a complete bounded pair-extension list in the actual full integer ring.
-- source:
--   D1Bound5/PairExtensionComplete.lean, lines 10-111, SHA-256 924ab489e8d75168ec90c999dcbd5d27e2d982db7928a79976af846ca6b835a6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.pairClosure_complete_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {tau nu : ℤ} (hd : 0 < discriminant tau nu)
    (e : QuadInt tau nu ≃+* 𝓞 K) (a b : QuadInt tau nu)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a*b+1 ≠ 0)
    (hroot : ∃ r0, r0*r0 = a*b+1)
    (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8)
    (bound : ℤ) (vertices : List (QuadInt tau nu))
    (hseeds : ∀ z, PairExtension a b z → z.norm ≤ 1089 → z ∈ vertices)
    (hclosed : ∀ z ∈ vertices, ∀ w,
      (w = pairMutationPlus a b z ∨ w = pairMutationMinus a b z) →
      w.norm ≤ bound → w ∈ vertices)
    (z : QuadInt tau nu) (hz : PairExtension a b z) (hNz : z.norm ≤ bound) :
    z ∈ vertices := by sorry

end D1Bound5
end
