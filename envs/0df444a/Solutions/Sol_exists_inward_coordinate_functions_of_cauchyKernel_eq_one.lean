-- Prove2me | solution 1 for exists_inward_coordinate_functions_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:23:14.836742+00:00
-- url     : https://prove2.me/submissions/a4a451de-e6b7-4cfd-95cb-660b789bd172

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_exists_inward_coordinate_functions

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ w ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega w = 1)
    {c : ℂ} (hc : c ∈ Omega.carrier) :
    ∃ radius : ℂ → ℝ, ∃ endpoint : ℂ → ℂ,
      (∀ z ∈ Omega.carrier,
        radius z ∈ Ioc (0 : ℝ) 1 ∧
        endpoint z ∈ frontier Omega.carrier ∧
        smoothJordanInwardPoint c (endpoint z) (radius z) = z) ∧
      ∀ xi ∈ frontier Omega.carrier,
        Filter.Tendsto (fun z => (radius z, endpoint z))
          (nhdsWithin xi Omega.carrier)
          (nhdsWithin (0, xi)
            (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier)) := by
  exact exists_inward_coordinate_functions Omega
    (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel) hc
