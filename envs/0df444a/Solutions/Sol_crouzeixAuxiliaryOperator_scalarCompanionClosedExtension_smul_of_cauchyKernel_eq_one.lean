-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:20:11.422834+00:00
-- url     : https://prove2.me/submissions/c59fffd2-4388-4cd8-9e5e-aacaa8df8cfa

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_crouzeixAuxiliaryOperator_congr_frontier
import Theorems.Thm_crouzeixAuxiliaryOperator_smul
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one


set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (a : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p)) =
      star a • crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension Omega p) := by
  calc
    crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p)) =
        crouzeixAuxiliaryOperator A Omega
          (fun z => star a •
            crouzeixPolynomialScalarCompanionClosedExtension Omega p z) := by
      apply crouzeixAuxiliaryOperator_congr_frontier
      intro z hz
      change crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z =
        star a • crouzeixPolynomialScalarCompanionClosedExtension Omega p z
      rw [smul_eq_mul,
        crouzeixPolynomialScalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
          Omega a p hkernel (frontier_subset_closure hz)]
    _ = star a • crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) :=
      crouzeixAuxiliaryOperator_smul A Omega (star a)
        (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
