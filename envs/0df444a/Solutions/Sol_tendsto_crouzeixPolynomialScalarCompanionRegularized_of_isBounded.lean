-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:46.194775+00:00
-- url     : https://prove2.me/submissions/0353afed-c9f2-42d7-a11a-5f77e793bf30

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_inward_coordinates
import Theorems.Thm_exists_inward_coordinate_functions

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  have hfrontier : Omega.boundaryParam 0 ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self 0
  have hcarrier : Omega.carrier.Nonempty :=
    Set.Nonempty.of_closure
      ⟨Omega.boundaryParam 0, frontier_subset_closure hfrontier⟩
  obtain ⟨c, hc⟩ := hcarrier
  obtain ⟨radius, endpoint, hcoord, hparam⟩ :=
    exists_inward_coordinate_functions Omega hbounded hc
  apply
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_inward_coordinates
      Omega p hkernel hc hxi radius endpoint
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hcoord z hz).2.2
  · exact hparam xi hxi
