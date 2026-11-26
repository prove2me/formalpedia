-- Prove2me | solution 1 for spectrum_affine_smul_one_subset_convex_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:49.230345+00:00
-- url     : https://prove2.me/submissions/d076a366-0134-468c-bed0-15858f23e018

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_spectrum_subset_closure_numericalRange
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
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    spectrum ℂ (c • (1 : E →L[ℂ] E) +
      (r : ℂ) • (A - c • (1 : E →L[ℂ] E))) ⊆ Omega.carrier := by
  have hop : c • (1 : E →L[ℂ] E) +
      (r : ℂ) • (A - c • (1 : E →L[ℂ] E)) =
      (((1 - r : ℝ) : ℂ) * c) • (1 : E →L[ℂ] E) + (r : ℂ) • A := by
    ext x
    simp only [add_apply, smul_apply, sub_apply, one_apply_eq_self]
    module
  have hspec : spectrum ℂ (c • (1 : E →L[ℂ] E) +
      (r : ℂ) • (A - c • (1 : E →L[ℂ] E))) =
      {(((1 - r : ℝ) : ℂ) * c)} + (r : ℂ) • spectrum ℂ A := by
    rw [hop, ← Algebra.algebraMap_eq_smul_one,
      ← spectrum.singleton_add_eq,
      spectrum.smul_eq_smul (r : ℂ) A (spectrum.nonempty A)]
  rw [hspec]
  rintro z ⟨a, ha, b, hb, rfl⟩
  rw [mem_singleton_iff] at ha
  subst a
  obtain ⟨lambda, hlambda, rfl⟩ := hb
  have hlambdaCarrier : lambda ∈ Omega.carrier :=
    hOmega (spectrum_subset_closure_numericalRange A hlambda)
  convert Omega.strictConvex_carrier.convex hc hlambdaCarrier
    (sub_nonneg.mpr hr.2) hr.1 (by ring) using 1
  apply Complex.ext <;>
    simp only [ofReal_sub, ofReal_one, smul_eq_mul, add_re, add_im, mul_re,
      mul_im, sub_re, one_re, ofReal_re, sub_im, one_im, ofReal_im,
      sub_self, zero_mul, sub_zero, add_zero, real_smul]
