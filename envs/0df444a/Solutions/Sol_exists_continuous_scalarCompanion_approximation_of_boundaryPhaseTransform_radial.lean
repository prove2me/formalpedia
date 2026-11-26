-- Prove2me | solution 1 for exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:46.988636+00:00
-- url     : https://prove2.me/submissions/1265a7e3-a2d5-449e-9af8-224b0a3d7c35

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform_radial
import Theorems.Thm_polynomialSupNorm_closure_carrier_eq_frontier


set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    (r : ℕ → Polynomial ℂ)
    (happrox : ∀ (j : ℕ) (z : ℂ), z ∈ closure Omega.carrier →
      ‖Polynomial.eval z (r j) -
          crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
        1 / ((j : ℝ) + 1))
    (hPlemelj :
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p) :
    ∃ (g : ℂ → ℂ) (q : ℕ → Polynomial ℂ),
      ContinuousOn g
          (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) ∧
      (∀ z ∈ closure Omega.carrier,
        ‖g z‖ ≤ polynomialSupNorm p (closure Omega.carrier)) ∧
      (∀ (j : ℕ) (z : ℂ), z ∈ closure Omega.carrier →
        ‖Polynomial.eval z (q j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
      crouzeixAuxiliaryOperator A Omega g =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by
  have hbounded : Bornology.IsBounded Omega.carrier :=
    Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel
  refine ⟨
    crouzeixPolynomialScalarCompanionClosedExtension Omega p,
    r, ?_, ?_, happrox, hPlemelj⟩
  · apply
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
        Omega p hbounded hkernel).mono
    rintro z ⟨t, _ht, rfl⟩
    apply frontier_subset_closure
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  · intro z hz
    calc
      ‖crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
          polynomialSupNorm p (frontier Omega.carrier) :=
        norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform_radial
          Omega p hkernel hphase hz
      _ = polynomialSupNorm p (closure Omega.carrier) :=
        (polynomialSupNorm_closure_carrier_eq_frontier
          Omega p hbounded).symm
