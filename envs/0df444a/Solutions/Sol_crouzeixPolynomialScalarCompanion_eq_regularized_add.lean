-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanion_eq_regularized_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:40:03.741812+00:00
-- url     : https://prove2.me/submissions/f22f61d4-9215-46e5-815f-9aa22edc7972

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_contourIntegral_add
import Theorems.Thm_contourIntegral_const_mul

section
open Complex Filter MeasureTheory Set
open scoped Interval Real
private theorem contourIntegrable_crouzeixScalarCauchyKernel
    (Omega : SmoothJordanDomain) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    ContourIntegrable (fun sigma ↦ (sigma - z)⁻¹) Omega.boundaryParam := by
  apply ContourIntegrable.of_continuousOn
  · exact Omega.boundaryParam_contDiff.continuous.continuousOn
  · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  · have hden : ContinuousOn (fun sigma : ℂ ↦ sigma - z)
        (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) :=
      continuous_id.continuousOn.sub continuous_const.continuousOn
    apply hden.inv₀
    rintro sigma ⟨t, ht, rfl⟩ hzero
    apply hz
    have heq : Omega.boundaryParam t = z := sub_eq_zero.mp hzero
    rw [← heq, ← Omega.boundaryParam_range]
    exact mem_range_self t
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
private theorem contourIntegrable_crouzeixScalarCauchyKernel_const_mul
    (Omega : SmoothJordanDomain) (c : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    ContourIntegrable (fun sigma ↦ c * (sigma - z)⁻¹)
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
    exact continuous_const.continuousOn.mul (hden.inv₀ hne)
end

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega p z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z +
        star (Polynomial.eval xi p) * crouzeixScalarCauchyKernel Omega z := by
  have hreg :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized
      Omega p xi hz
  have hkernel := contourIntegrable_crouzeixScalarCauchyKernel Omega hz
  have hconst := contourIntegrable_crouzeixScalarCauchyKernel_const_mul
    Omega (star (Polynomial.eval xi p)) hz
  have hfun :
      (fun sigma ↦ star (Polynomial.eval sigma p) * (sigma - z)⁻¹) =
        (fun sigma ↦
          (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
              (sigma - z)⁻¹ +
            star (Polynomial.eval xi p) * (sigma - z)⁻¹) := by
    funext sigma
    ring
  unfold crouzeixPolynomialScalarCompanion
    crouzeixPolynomialScalarCompanionRegularized crouzeixScalarCauchyKernel
  rw [hfun, contourIntegral_add hreg hconst,
    contourIntegral_const_mul (star (Polynomial.eval xi p)) hkernel]
  ring
