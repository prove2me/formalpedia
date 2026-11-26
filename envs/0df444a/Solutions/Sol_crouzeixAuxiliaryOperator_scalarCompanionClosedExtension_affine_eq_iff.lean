-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_affine_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:24:24.912587+00:00
-- url     : https://prove2.me/submissions/10807f50-f888-496a-8afd-55de1ce406ee

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_eq_iff
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_eq_iff

set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    (crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension
            Omega (a • p + Polynomial.C b)) =
        crouzeixPolynomialAuxiliaryOperator A Omega
          (a • p + Polynomial.C b)) ↔
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by
  exact
    (crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_eq_iff
      A Omega (a • p) b hOmega hkernel).trans
        (crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_eq_iff
          A Omega ha p hkernel)
