-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:29.656061+00:00
-- url     : https://prove2.me/submissions/d0ff67b2-bada-49a5-89e5-da4592344364

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_sub_self_joint
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionRegularized_self
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
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
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun x : ℝ × ℂ =>
        crouzeixPolynomialScalarCompanionRegularized Omega p x.2
          (smoothJordanInwardPoint c x.2 x.1))
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  let l : Filter (ℝ × ℂ) := nhdsWithin (0, xi)
    (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier)
  have herror :=
    tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_sub_self_joint
      Omega p hc hxi
  have hl : l ≤ nhds (0, xi) := by
    dsimp only [l, nhdsWithin]
    exact inf_le_left
  have hproj : Filter.Tendsto (fun x : ℝ × ℂ => x.2) l
      (nhdsWithin xi (frontier Omega.carrier)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only using continuous_snd.continuousAt.tendsto.mono_left hl
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact hx.2
  have hself : Filter.Tendsto
      (fun x : ℝ × ℂ =>
        crouzeixPolynomialScalarCompanionRegularized Omega p x.2 x.2)
      l
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) :=
    (continuousOn_crouzeixPolynomialScalarCompanionRegularized_self
      Omega p xi hxi).tendsto.comp hproj
  have hadd := herror.add hself
  simpa only [l, zero_add] using hadd.congr'
    (Filter.Eventually.of_forall fun x => by ring)
