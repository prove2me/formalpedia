-- Prove2me | Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring
-- name    : D1Bound5.small_pair_graph_excludes_three_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:15.829306+00:00
-- url     : https://prove2.me/theorems/3d5c8cb3-3318-4a31-9495-35f1c5d409fa
-- title:
--   Small pair graph excludes three full ring
-- statement:
--   Complete finite-graph exclusion for actual full-ring common extensions. Every input hypothesis is either mathematical anchor data or a finite, kernel-checkable seed, closure, filtering or triangle certificate.
-- source:
--   D1Bound5/SmallPairGraphCheck.lean, lines 60-96, SHA-256 a1fd39ac1e63a1a407d5fbedb3ad3d7599b1489a8857fc7d2c2d3c2c9b4396e6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt








theorem _root_.D1Bound5.small_pair_graph_excludes_three_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {tau nu : ℤ} (hd : 0 < discriminant tau nu)
    (e : QuadInt tau nu ≃+* 𝓞 K) (a b : QuadInt tau nu)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a*b+1 ≠ 0)
    (hroot : ∃ r0, r0*r0 = a*b+1) (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8)
    (bound : ℤ) (roots vertices large : List (QuadInt tau nu))
    (sieve : List (ℕ × ℕ)) (hvalid : CoordinateSquareSieveValid tau nu sieve)
    (hrootdisk : ∀ q ∈ disk tau nu 132, q ∈ roots)
    (hseeds : pairSeedsCoveredBool a b roots vertices = true)
    (hclosed : pairClosureBool a b bound vertices = true)
    (hfilter : largePairVertices a b vertices = large)
    (htriangle : pairGraphTriangleFreeBool sieve large = true)
    (t : Fin 3 → QuadInt tau nu) (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension a b (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm)
    (hbound : ∀ i, (t i).norm ≤ bound)
    (hneA : ∀ i, t i ≠ a) (hneB : ∀ i, t i ≠ b) : False := by sorry

end D1Bound5
end
