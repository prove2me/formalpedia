-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:55.683667+00:00
-- url     : https://prove2.me/submissions/15ad2698-7437-4606-83a6-e9fdcd9aa07a

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_add_of_isBounded
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (p + Polynomial.C a) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z + star a := by
  rw [
    crouzeixPolynomialScalarCompanionClosedExtension_add_of_isBounded
      Omega p (Polynomial.C a) hbounded hkernel hz,
    crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
      Omega a hbounded hkernel hz]
