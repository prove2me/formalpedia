-- Prove2me | solution 1 for exists_inward_coordinate_functions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:23.83199+00:00
-- url     : https://prove2.me/submissions/e4449a18-c60b-4c12-9d70-c8d41b34ff11

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_exists_inward_coordinates
import Theorems.Thm_exists_uniform_inward_boundary_denominator_bound
import Theorems.Thm_exists_uniform_inward_boundary_cross_bound
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
    (Omega : SmoothJordanDomain)
    (hbounded : Bornology.IsBounded Omega.carrier)
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
  have hex : ∀ z : ℂ, ∃ r : ℝ, ∃ eta : ℂ,
      z ∈ Omega.carrier →
        r ∈ Ioc (0 : ℝ) 1 ∧ eta ∈ frontier Omega.carrier ∧
          smoothJordanInwardPoint c eta r = z := by
    intro z
    by_cases hz : z ∈ Omega.carrier
    · obtain ⟨r, hr, eta, heta, heq⟩ :=
        exists_inward_coordinates Omega hbounded hc hz
      exact ⟨r, eta, fun _ => ⟨hr, heta, heq⟩⟩
    · exact ⟨1, Omega.boundaryParam 0, fun hz' => (hz hz').elim⟩
  choose radius endpoint hcoord using hex
  refine ⟨radius, endpoint, ?_, ?_⟩
  · intro z hz
    exact hcoord z hz
  · intro xi hxi
    let l : Filter ℂ := nhdsWithin xi Omega.carrier
    obtain ⟨delta, R, hdelta, _hR, hcross⟩ :=
      exists_uniform_inward_boundary_cross_bound Omega hc
    obtain ⟨delta', hdelta', hden⟩ :=
      exists_uniform_inward_boundary_denominator_bound Omega hc
    have hl : l ≤ nhds xi := by
      dsimp only [l, nhdsWithin]
      exact inf_le_left
    have hdist : Filter.Tendsto (fun z : ℂ => ‖xi - z‖ / delta') l
        (nhds 0) := by
      have hcont : ContinuousAt (fun z : ℂ => ‖xi - z‖ / delta') xi := by
        fun_prop
      simpa only [sub_self, norm_zero, zero_div] using
        hcont.tendsto.mono_left hl
    have hradius : Filter.Tendsto radius l (nhds 0) := by
      apply squeeze_zero'
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact (hcoord z hz).1.1.le
      · filter_upwards [self_mem_nhdsWithin] with z hz
        obtain ⟨hr, heta, heq⟩ := hcoord z hz
        apply (le_div_iff₀ hdelta').2
        simpa only [heq] using hden (endpoint z) heta (radius z) hr xi hxi
      · exact hdist
    have hendpointMajorant : Filter.Tendsto
        (fun z : ℂ => (R / delta + 1) * ‖xi - z‖) l (nhds 0) := by
      have hcont : Filter.Tendsto (fun z : ℂ => ‖xi - z‖) l (nhds 0) := by
        have hc' : ContinuousAt (fun z : ℂ => ‖xi - z‖) xi := by fun_prop
        simpa only [sub_self, norm_zero] using hc'.tendsto.mono_left hl
      simpa only [mul_zero] using tendsto_const_nhds.mul hcont
    have hendpointDist : Filter.Tendsto
        (fun z : ℂ => dist (endpoint z) xi) l (nhds 0) := by
      apply squeeze_zero'
        (g := fun z : ℂ => (R / delta + 1) * ‖xi - z‖)
      · exact Filter.Eventually.of_forall fun _ => dist_nonneg
      · filter_upwards [self_mem_nhdsWithin] with z hz
        obtain ⟨hr, heta, heq⟩ := hcoord z hz
        have hfirst : ‖endpoint z - z‖ ≤
            (R / delta) * ‖xi - z‖ := by
          calc
            ‖endpoint z - z‖ ≤ (R * ‖xi - z‖) / delta := by
              apply (le_div_iff₀ hdelta).2
              simpa only [heq, mul_comm, norm_sub_rev] using
                hcross (endpoint z) heta (radius z) hr xi hxi
            _ = (R / delta) * ‖xi - z‖ := by ring
        rw [dist_eq_norm]
        calc
          ‖endpoint z - xi‖ ≤ ‖endpoint z - z‖ + ‖z - xi‖ := by
            simpa only [dist_eq_norm] using dist_triangle (endpoint z) z xi
          _ ≤ (R / delta) * ‖xi - z‖ + ‖xi - z‖ := by
            gcongr
            exact (norm_sub_rev z xi).le
          _ = (R / delta + 1) * ‖xi - z‖ := by ring
      · exact hendpointMajorant
    have hendpoint : Filter.Tendsto endpoint l (nhds xi) :=
      tendsto_iff_dist_tendsto_zero.2 hendpointDist
    apply tendsto_nhdsWithin_iff.mpr
    have hpair : Filter.Tendsto (fun z => (radius z, endpoint z)) l
        (nhds (0, xi)) := by
      rw [nhds_prod_eq]
      exact hradius.prodMk hendpoint
    refine ⟨hpair, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact ⟨(hcoord z hz).1, (hcoord z hz).2.1⟩
