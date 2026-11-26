-- Prove2me | solution 1 for contourIntegral_mul_inv_sub_eq_two_pi_I_mul_canonicalOrientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:30.091201+00:00
-- url     : https://prove2.me/submissions/ad484ba4-6b0b-4d24-85cf-7a450674e98f

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Theorems.Thm_contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_oriented_carrier
import Theorems.Thm_SmoothJordanDomain_canonicalNormal_support_all_of_support_at
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_exists_oriented_point_canonicalOrientation
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
open Complex Filter MeasureTheory Set
open scoped Interval Topology
theorem _root_.solution
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    contourIntegral (fun sigma => f sigma * (sigma - z)⁻¹)
        Omega.canonicalOrientation.boundaryParam =
      (2 * (Real.pi : ℂ) * I) * f z := by
  let Psi := Omega.canonicalOrientation
  have hfPsi : DiffContOnCl ℂ f Psi.carrier := by
    simpa only [Psi, SmoothJordanDomain.canonicalOrientation_carrier] using hf
  have hzPsi : z ∈ Psi.carrier := by
    simpa only [Psi, SmoothJordanDomain.canonicalOrientation_carrier] using hz
  obtain ⟨c, hc, hc0⟩ := Omega.exists_oriented_point_canonicalOrientation
  have hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Psi.boundaryParam t) *
        (c - Psi.boundaryParam t)).re ≤ 0 :=
    Psi.canonicalNormal_support_all_of_support_at c hc 0 hc0
  exact contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_oriented_carrier
    Psi hfPsi c hc hcside hzPsi
