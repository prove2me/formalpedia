-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionRegularized_add_of_not_mem_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:03.12556+00:00
-- url     : https://prove2.me/submissions/4c9bd643-c247-4cf6-a538-2b372c850dfd

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_contourIntegral_add
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
section
open Complex Filter MeasureTheory Set
open scoped Interval Real
private theorem contourIntegrable_crouzeixPolynomialScalarCompanionRegularized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    ContourIntegrable
      (fun sigma ↦
        (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
          (sigma - z)⁻¹)
      Omega.boundaryParam := by
  apply ContourIntegrable.of_continuousOn
  · exact Omega.boundaryParam_contDiff.continuous.continuousOn
  · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  · have hden : ContinuousOn (fun sigma : ℂ ↦ sigma - z)
        (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) :=
      continuous_id.continuousOn.sub continuous_const.continuousOn
    have hne : ∀ sigma ∈
        Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi), sigma - z ≠ 0 := by
      rintro sigma ⟨t, ht, rfl⟩ hzero
      apply hz
      have heq : Omega.boundaryParam t = z := sub_eq_zero.mp hzero
      rw [← heq, ← Omega.boundaryParam_range]
      exact mem_range_self t
    exact (p.continuous.star.continuousOn.sub
      continuous_const.continuousOn).mul (hden.inv₀ hne)
end

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (xi : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionRegularized Omega (p + q) xi z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z +
        crouzeixPolynomialScalarCompanionRegularized Omega q xi z := by
  have hp := contourIntegrable_crouzeixPolynomialScalarCompanionRegularized
    Omega p xi hz
  have hq := contourIntegrable_crouzeixPolynomialScalarCompanionRegularized
    Omega q xi hz
  have hfun :
      (fun sigma ↦
        (star (Polynomial.eval sigma (p + q)) -
            star (Polynomial.eval xi (p + q))) * (sigma - z)⁻¹) =
        fun sigma ↦
          (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
              (sigma - z)⁻¹ +
            (star (Polynomial.eval sigma q) - star (Polynomial.eval xi q)) *
              (sigma - z)⁻¹ := by
    funext sigma
    simp only [Polynomial.eval_add, star_add]
    ring
  unfold crouzeixPolynomialScalarCompanionRegularized
  rw [hfun, contourIntegral_add hp hq]
  ring
