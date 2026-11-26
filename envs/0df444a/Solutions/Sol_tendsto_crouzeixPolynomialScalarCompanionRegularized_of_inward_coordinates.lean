-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanionRegularized_of_inward_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:56.333557+00:00
-- url     : https://prove2.me/submissions/e9098b8b-9a9b-4a42-b722-ee61023fe92d

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_of_inward_coordinates
import Theorems.Thm_crouzeixPolynomialScalarCompanion_eq_regularized_add


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {c xi : ℂ} (hc : c ∈ Omega.carrier)
    (hxi : xi ∈ frontier Omega.carrier)
    (radius : ℂ → ℝ) (endpoint : ℂ → ℂ)
    (hcoord : ∀ᶠ z in nhdsWithin xi Omega.carrier,
      smoothJordanInwardPoint c (endpoint z) (radius z) = z)
    (hparam : Filter.Tendsto (fun z => (radius z, endpoint z))
      (nhdsWithin xi Omega.carrier)
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))) :
    Filter.Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  have hfull :=
    tendsto_crouzeixPolynomialScalarCompanion_of_inward_coordinates
      Omega p hkernel hc hxi radius endpoint hcoord hparam
  have hsub := hfull.sub
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℂ => star (Polynomial.eval xi p))
      (nhdsWithin xi Omega.carrier)
      (nhds (star (Polynomial.eval xi p))))
  have htarget :
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi -
          star (Polynomial.eval xi p) =
        crouzeixPolynomialScalarCompanionRegularized Omega p xi xi := by
    unfold crouzeixPolynomialScalarCompanionBoundaryValue
    ring
  rw [htarget] at hsub
  apply hsub.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzfrontier : z ∉ frontier Omega.carrier := by
    intro hzfrontier
    have hempty : z ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact hempty
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p xi
    hzfrontier, hkernel z hz, mul_one]
  ring
