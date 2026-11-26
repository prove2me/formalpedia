-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:57.149047+00:00
-- url     : https://prove2.me/submissions/ce344fa9-48d6-4c35-a143-ce179ae0863a

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary


set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Filter.Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  apply norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary
    Omega p (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      hbounded
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
        Omega p hkernel hreg)
      (fun _ hw ↦
        crouzeixPolynomialScalarCompanionClosedExtension_eq Omega p hw)
      (fun xi hxi ↦ ?_) hz
  rw [
    crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
      Omega p hkernel hreg hxi,
    crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform]
  exact hphase xi hxi
