-- Prove2me | Theorems.Thm_D1Bound5_PellFiniteCertificate_full_ring_member
-- name    : D1Bound5.PellFiniteCertificate.full_ring_member
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:19:14.384899+00:00
-- url     : https://prove2.me/theorems/2d4c4d05-2d0e-4653-b054-487b3e2ee9a4
-- title:
--   Pell Finite Certificate — full ring member
-- statement:
--   Closed radius X^2 is represented by squared complex norm at most X^4. Both signs of each real Pell extension are retained.
-- source:
--   D1Bound5/PellFiniteCertificate.lean, lines 51-91, SHA-256 dcc2fd88b881b2c8eafcbde15c1cb33b51af6fe491a0856432d4dcd395c5e1ed. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairRealReduction_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5








theorem _root_.D1Bound5.PellFiniteCertificate.full_ring_member
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ) {d X : ℤ}
    (C : PellFiniteCertificate d X) (hd : 7 ≤ d) (hX : 1 ≤ X)
    (z : 𝓞 K) (hreal : UnitPairRealDescription d z)
    (hbound : ‖phi (z : K)‖^2 ≤ (X : ℝ)^4) :
    ∃ m : ℤ, z=(m : 𝓞 K) ∧ PellSignedMember C.graph.magnitudes m := by sorry



end D1Bound5
end
