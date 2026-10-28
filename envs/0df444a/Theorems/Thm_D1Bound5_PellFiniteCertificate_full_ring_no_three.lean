-- Prove2me | Theorems.Thm_D1Bound5_PellFiniteCertificate_full_ring_no_three
-- name    : D1Bound5.PellFiniteCertificate.full_ring_no_three
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:31:58.869901+00:00
-- url     : https://prove2.me/theorems/4d65cc8b-e3d6-4e44-baca-5ba20e19f774
-- title:
--   Pell Finite Certificate — full ring no three
-- statement:
--   The complete finite theorem in the actual full ring. Its only finite input is a concrete kernel-checked certificate whose list is proved complete by the ordinary continued-fraction theorem.
-- source:
--   D1Bound5/PellFiniteCertificate.lean, lines 93-116, SHA-256 dcc2fd88b881b2c8eafcbde15c1cb33b51af6fe491a0856432d4dcd395c5e1ed. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairRealReduction_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5










theorem _root_.D1Bound5.PellFiniteCertificate.full_ring_no_three
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (M : UnitPairArithmeticModel (𝓞 K)) {X : ℤ}
    (C : PellFiniteCertificate M.d X) (hd : 7 ≤ M.d) (hX : 1 ≤ X)
    (t : Fin 3 → 𝓞 K) (ht : IsD1Tuple t)
    (hreal : ∀ i, UnitPairRealDescription M.d (t i))
    (hbound : ∀ i, ‖phi (t i : K)‖^2 ≤ (X : ℝ)^4) : False := by sorry

end D1Bound5
end
