-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:20.537498+00:00
-- url     : https://prove2.me/submissions/2e095db1-ed56-4cbb-902c-07676f1e5006

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Theorems.Thm_analyticOn_crouzeixPolynomialScalarCompanion


set_option autoImplicit false
open Complex Filter Set
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p z =
      crouzeixPolynomialScalarCompanion Omega p z := by
  apply extendFrom_extends
    (analyticOn_crouzeixPolynomialScalarCompanion Omega p).continuousOn z hz
