-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_affine_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:24:16.373491+00:00
-- url     : https://prove2.me/submissions/c2e002ae-da35-4362-9878-808f92b282aa

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_of_cauchyKernel_eq_one

set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (a b : ℂ) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (a • p + Polynomial.C b)) =
      star a • crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) +
        crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C b) := by
  rw [
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_of_cauchyKernel_eq_one
      A Omega (a • p) b hOmega hkernel,
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
      A Omega a p hkernel]
