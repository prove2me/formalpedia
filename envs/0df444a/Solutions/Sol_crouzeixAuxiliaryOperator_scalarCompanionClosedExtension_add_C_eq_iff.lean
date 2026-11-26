-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:12.465479+00:00
-- url     : https://prove2.me/submissions/b7791602-477d-496d-8225-29e35b1471dc

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_add


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
    (crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension
            Omega (p + Polynomial.C a)) =
        crouzeixPolynomialAuxiliaryOperator A Omega
          (p + Polynomial.C a)) ↔
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by
  rw [
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_of_cauchyKernel_eq_one
      A Omega p a hOmega hkernel,
    crouzeixPolynomialAuxiliaryOperator_add
      A Omega p (Polynomial.C a) hOmega]
  constructor
  · intro h
    exact add_right_cancel h
  · intro h
    exact congrArg
      (fun T : E →L[ℂ] E =>
        T + crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a)) h
