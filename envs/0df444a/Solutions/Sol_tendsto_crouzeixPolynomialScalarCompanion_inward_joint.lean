-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanion_inward_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:47.552519+00:00
-- url     : https://prove2.me/submissions/d6273366-5756-4ba7-a1ae-41194f367733

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_smoothJordanInwardPoint_mem_carrier
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_joint
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_eq_regularized_add
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



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
      (fun x : ℝ × ℂ =>
        crouzeixPolynomialScalarCompanion Omega p
          (smoothJordanInwardPoint c x.2 x.1))
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by
  let l : Filter (ℝ × ℂ) := nhdsWithin (0, xi)
    (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier)
  have hl : l ≤ nhds (0, xi) := by
    dsimp only [l, nhdsWithin]
    exact inf_le_left
  have heval : Filter.Tendsto
      (fun x : ℝ × ℂ => star (Polynomial.eval x.2 p)) l
      (nhds (star (Polynomial.eval xi p))) := by
    have hcont : Continuous (fun x : ℝ × ℂ =>
        star (Polynomial.eval x.2 p)) := by fun_prop
    exact hcont.continuousAt.tendsto.mono_left hl
  have hreg :=
    tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_joint
      Omega p hc hxi
  have hadd := heval.add hreg
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  apply hadd.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hz : smoothJordanInwardPoint c x.2 x.1 ∈ Omega.carrier :=
    smoothJordanInwardPoint_mem_carrier Omega hc hx.2 hx.1
  have hzfrontier : smoothJordanInwardPoint c x.2 x.1 ∉
      frontier Omega.carrier := by
    intro hzfrontier
    have hempty : smoothJordanInwardPoint c x.2 x.1 ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact hempty
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p x.2
    hzfrontier, hkernel _ hz, mul_one]
  exact add_comm _ _
