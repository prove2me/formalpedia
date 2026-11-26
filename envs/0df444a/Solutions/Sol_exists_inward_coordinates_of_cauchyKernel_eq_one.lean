-- Prove2me | solution 1 for exists_inward_coordinates_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:22:56.691481+00:00
-- url     : https://prove2.me/submissions/b366cd0f-a829-44b7-8826-477f3a48ecf5

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_exists_inward_coordinates

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ w ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega w = 1)
    {c z : ℂ} (hc : c ∈ Omega.carrier) (hz : z ∈ Omega.carrier) :
    ∃ r ∈ Ioc (0 : ℝ) 1, ∃ eta ∈ frontier Omega.carrier,
      smoothJordanInwardPoint c eta r = z := by
  exact exists_inward_coordinates Omega
    (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel) hc hz
