-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_affine_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:23:53.568069+00:00
-- url     : https://prove2.me/submissions/addcf641-0b10-4076-880e-a105619a1a4f

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a b : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (a • p + Polynomial.C b) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        star b := by
  rw [
    crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
      Omega (a • p) b
        (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel) hkernel hz,
    crouzeixPolynomialScalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
      Omega a p hkernel hz]
