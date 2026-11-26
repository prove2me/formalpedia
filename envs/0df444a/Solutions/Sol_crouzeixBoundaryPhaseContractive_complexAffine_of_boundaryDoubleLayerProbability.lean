-- Prove2me | solution 1 for crouzeixBoundaryPhaseContractive_complexAffine_of_boundaryDoubleLayerProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:35:01.614095+00:00
-- url     : https://prove2.me/submissions/4ab2a3d3-ff5e-461a-9d9d-2410afc7b22f

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
import Theorems.Thm_SmoothJordanDomain_frontier_complexAffine
import Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_complexAffine
import Theorems.Thm_intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_complexAffine_iff
import Theorems.Thm_integral_crouzeixBoundaryDoubleLayerDensity_complexAffine
import Theorems.Thm_crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
import Theorems.Thm_intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one


set_option autoImplicit false
open Complex MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a b : ℂ) (ha : a ≠ 0)
    (p : Polynomial ℂ)
    (hmass : ∀ xi ∈ frontier Omega.carrier,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hpos : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t) :
    CrouzeixBoundaryPhaseContractive (Omega.complexAffine a b ha) p := by
  apply crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
  · intro xi' hxi'
    rw [Omega.frontier_complexAffine a b ha] at hxi'
    obtain ⟨xi, hxi, rfl⟩ := hxi'
    rw [
      intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_complexAffine_iff]
    exact
      intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
        Omega xi (hmass xi hxi)
  · intro xi' hxi'
    rw [Omega.frontier_complexAffine a b ha] at hxi'
    obtain ⟨xi, hxi, rfl⟩ := hxi'
    rw [integral_crouzeixBoundaryDoubleLayerDensity_complexAffine]
    exact hmass xi hxi
  · intro xi' hxi'
    rw [Omega.frontier_complexAffine a b ha] at hxi'
    obtain ⟨xi, hxi, rfl⟩ := hxi'
    intro t ht
    rw [crouzeixBoundaryDoubleLayerDensity_complexAffine]
    exact hpos xi hxi t ht
