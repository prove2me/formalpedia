-- Prove2me | solution 1 for contourIntegral_resolvent_eq_scalar_of_convex_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:38.637147+00:00
-- url     : https://prove2.me/submissions/6ccb7d71-8c6d-4f23-b5d0-f63227972a5b

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_contourIntegral_resolvent_affineOperator_eq_of_boundary_subset_resolventSet
import Theorems.Thm_spectrum_affine_smul_one_subset_convex_carrier
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    [Nontrivial E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    contourIntegral (resolvent A) Omega.boundaryParam =
      contourIntegral (resolvent (c • (1 : E →L[ℂ] E)))
        Omega.boundaryParam := by
  let B : E →L[ℂ] E := c • 1
  let D : E →L[ℂ] E := A - c • 1
  have hBD : Commute B D := by
    dsimp only [B, D]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      Algebra.commute_algebraMap_left c (A - c • (1 : E →L[ℂ] E))
  have hres : ∀ r ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + (r : ℂ) • D) := by
    intro r hr t
    rw [mem_resolventSet_iff, ← spectrum.notMem_iff]
    intro hspectrum
    have hcarrier : Omega.boundaryParam t ∈ Omega.carrier :=
      spectrum_affine_smul_one_subset_convex_carrier
        A Omega c hc hOmega r hr hspectrum
    have hfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self t
    have hempty : Omega.boundaryParam t ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hcarrier, hfrontier⟩
    exact hempty
  have hhom :=
    contourIntegral_resolvent_affineOperator_eq_of_boundary_subset_resolventSet
      B D Omega hBD hres
  have hsum : B + D = A := by
    dsimp only [B, D]
    abel
  simpa only [hsum, B] using hhom
