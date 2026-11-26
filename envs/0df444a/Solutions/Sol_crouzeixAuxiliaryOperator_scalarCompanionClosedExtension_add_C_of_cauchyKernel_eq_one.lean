-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:00.626654+00:00
-- url     : https://prove2.me/submissions/c609de2e-ab62-4606-b044-1f938b752072

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_cauchyKernel_eq_one
import Theorems.Thm_contourIntegral_add
import Theorems.Thm_crouzeixAuxiliaryIntegrand_contourIntegrable
import Theorems.Thm_crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) (a : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (p + Polynomial.C a)) =
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) +
        crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) := by
  let g := crouzeixPolynomialScalarCompanionClosedExtension Omega p
  have hgcont : ContinuousOn g
      (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) := by
    apply
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_cauchyKernel_eq_one
        Omega p hkernel).mono
    rintro z ⟨t, _ht, rfl⟩
    apply frontier_subset_closure
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hgint :=
    crouzeixAuxiliaryIntegrand_contourIntegrable A Omega g hOmega hgcont
  have haint :=
    crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable
      A Omega (Polynomial.C a) hOmega
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  rw [← smul_add, ← contourIntegral_add hgint haint]
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have hfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  change deriv Omega.boundaryParam t •
      (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (p + Polynomial.C a) (Omega.boundaryParam t) •
        resolvent A (Omega.boundaryParam t)) =
    deriv Omega.boundaryParam t •
      ((g (Omega.boundaryParam t) • resolvent A (Omega.boundaryParam t)) +
        (star (Polynomial.eval (Omega.boundaryParam t) (Polynomial.C a)) •
          resolvent A (Omega.boundaryParam t)))
  rw [
    crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
      Omega p a
        (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel (frontier_subset_closure hfrontier)]
  simp only [g, Polynomial.eval_C, add_smul, smul_add]
