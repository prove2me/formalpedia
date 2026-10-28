-- Prove2me | Theorems.Thm_D1Bound5_full_ring_coherent_two_nonzero_and_one_le_norm
-- name    : D1Bound5.full_ring_coherent_two_nonzero_and_one_le_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:56.731687+00:00
-- url     : https://prove2.me/theorems/f8f6edb2-6e7d-47db-9bd5-5f56da2fa22e
-- title:
--   Full ring coherent two nonzero and one le norm
-- statement:
--   The arithmetic and analytic bridges combined for actual tuple entries. The paper's size assumptions force the coherent form nonzero and therefore give its integral lower bound, with neither fact assumed.
-- source:
--   D1Bound5/CoherentTwoSize.lean, lines 148-220, SHA-256 8a8f6db3352296dc34c3bf72970d3d3c0c58939fc28136095cce2e2e458acdfa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_IsD1

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5










theorem _root_.D1Bound5.full_ring_coherent_two_nonzero_and_one_le_norm
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {T : Finset (𝓞 K)} (hT : IsD1 T) (a b p q : 𝓞 K)
    (ha : a ∈ T) (hb : b ∈ T) (hp : p ∈ T) (hq : q ∈ T)
    (hab : a ≠ b) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hpq : p ≠ q)
    (eta : ℂ) (heta : eta ^ 2 = phi (p : K) * phi (q : K))
    (hB : 3 ≤ ‖phi (b : K)‖) (hP : 5 * ‖phi (b : K)‖ ≤ ‖phi (p : K)‖)
    (hQ : 5 * ‖phi (a : K)‖ * ‖phi (b : K)‖ * ‖phi (p : K)‖ ≤ ‖phi (q : K)‖) :
    let L := coherentAnchorRoot (phi (a : K)) (phi (p : K)) (phi (q : K)) eta -
      coherentAnchorRoot (phi (b : K)) (phi (p : K)) (phi (q : K)) eta -
      (phi (a : K) - phi (b : K)) *
        coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta
    L ≠ 0 ∧ 1 ≤ ‖L‖ := by sorry

end D1Bound5
end
