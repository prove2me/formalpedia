-- Prove2me | solution 1 for crouzeixBoundaryDoubleLayerDensity_nonneg_of_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:23.467902+00:00
-- url     : https://prove2.me/submissions/d38bb503-fa33-49bb-9155-57b588e073b4

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
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
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (xi : ℂ) (t : ℝ)
    (hsupport :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (xi - Omega.boundaryParam t)).re ≤ 0) :
    0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t := by
  let D := deriv Omega.boundaryParam t
  let d := Omega.boundaryParam t - xi
  have hnormal : ((starRingEnd ℂ) (-I * D) * (-d)).re ≤ 0 := by
    simpa only [D, d, neg_sub] using hsupport
  have him : 0 ≤ (D * d⁻¹).im := by
    by_cases hd : d = 0
    · rw [hd, inv_zero, mul_zero, zero_im]
    have hnum : 0 ≤ D.im * d.re - D.re * d.im := by
      have hid : ((starRingEnd ℂ) (-I * D) * (-d)).re =
          -(D.im * d.re - D.re * d.im) := by
        simp only [map_mul, map_neg, Complex.conj_I, Complex.mul_re,
          Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
          Complex.I_im, Complex.conj_re, Complex.conj_im]
        ring
      rw [hid] at hnormal
      linarith
    rw [← div_eq_mul_inv, Complex.div_im, ← sub_div]
    exact div_nonneg hnum (Complex.normSq_nonneg d)
  exact div_nonneg him Real.pi_pos.le
