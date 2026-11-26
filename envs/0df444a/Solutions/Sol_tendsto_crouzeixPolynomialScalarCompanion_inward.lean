-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanion_inward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:23:01.602612+00:00
-- url     : https://prove2.me/submissions/22d4959f-4fa7-4de7-a6c8-6ff0fd346538

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_smoothJordanInwardPoint_mem_carrier
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_inward
import Theorems.Thm_crouzeixPolynomialScalarCompanion_eq_regularized_add


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {c xi : ℂ} (hc : c ∈ Omega.carrier)
    (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun r : ℝ ↦ crouzeixPolynomialScalarCompanion Omega p
        (smoothJordanInwardPoint c xi r))
      (nhdsWithin 0 (Ioc (0 : ℝ) 1))
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by
  have hreg :=
    tendsto_crouzeixPolynomialScalarCompanionRegularized_inward
      Omega p hc hxi
  have hlim : Filter.Tendsto
      (fun r : ℝ ↦ star (Polynomial.eval xi p) +
        crouzeixPolynomialScalarCompanionRegularized Omega p xi
          (smoothJordanInwardPoint c xi r))
      (nhdsWithin 0 (Ioc (0 : ℝ) 1))
      (nhds (star (Polynomial.eval xi p) +
        crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) :=
    tendsto_const_nhds.add hreg
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hz : smoothJordanInwardPoint c xi r ∈ Omega.carrier :=
    smoothJordanInwardPoint_mem_carrier Omega hc hxi hr
  have hzfrontier : smoothJordanInwardPoint c xi r ∉
      frontier Omega.carrier := by
    intro hzfrontier
    have hempty : smoothJordanInwardPoint c xi r ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact hempty
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p xi
    hzfrontier, hkernel _ hz, mul_one]
  exact add_comm _ _
