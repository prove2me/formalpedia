-- Prove2me | solution 1 for contourIntegral_polynomial_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:04.40077+00:00
-- url     : https://prove2.me/submissions/d8add6a5-9f2a-4ff0-874c-fceb0b649317

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_contourIntegral_add
import Theorems.Thm_contourIntegral_eq_zero_of_hasDerivAt_of_closed
import Theorems.Thm_contourIntegral_smul
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


section
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real
private theorem contourIntegral_pow_eq_zero
    (Omega : SmoothJordanDomain) (n : ℕ) :
    contourIntegral (fun z : ℂ => z ^ n) Omega.boundaryParam = 0 := by
  apply contourIntegral_eq_zero_of_hasDerivAt_of_closed
    (Fp := fun z : ℂ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
  · intro _ _
    exact
      (Omega.boundaryParam_contDiff.differentiable (by norm_num)).differentiableAt
  · intro t _
    convert (hasDerivAt_pow (n + 1) (Omega.boundaryParam t)).div_const
      ((n + 1 : ℕ) : ℂ) using 1
    · rfl
    · field_simp
      congr 1
  · apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · exact (continuous_pow n).continuousOn
  · simpa only [zero_add] using Omega.boundaryParam_periodic 0
private theorem contourIntegral_finset_sum_pow_mul_eq_zero
    (Omega : SmoothJordanDomain) (s : Finset ℕ)
    (k : ℕ → ℕ) (c : ℕ → ℂ) :
    contourIntegral (fun z : ℂ => ∑ j ∈ s, z ^ k j * c j)
      Omega.boundaryParam = 0 := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, smul_zero, contourIntegral,
        intervalIntegral.integral_zero]
  | @insert a s ha ih =>
      let f : ℂ → ℂ := fun z => z ^ k a * c a
      let g : ℂ → ℂ := fun z => ∑ j ∈ s, z ^ k j * c j
      have hf : ContourIntegrable f Omega.boundaryParam := by
        apply ContourIntegrable.of_continuousOn
        · exact Omega.boundaryParam_contDiff.continuous.continuousOn
        · exact
            (Omega.boundaryParam_contDiff.continuous_deriv
              (by norm_num)).continuousOn
        · exact ((continuous_pow (k a)).mul continuous_const).continuousOn
      have hg : ContourIntegrable g Omega.boundaryParam := by
        apply ContourIntegrable.of_continuousOn
        · exact Omega.boundaryParam_contDiff.continuous.continuousOn
        · exact
            (Omega.boundaryParam_contDiff.continuous_deriv
              (by norm_num)).continuousOn
        · exact
            (continuous_finsetSum s fun j _ =>
              (continuous_pow (k j)).mul continuous_const).continuousOn
      have hterm : contourIntegral f Omega.boundaryParam = 0 := by
        have hfun : f = fun z => c a • z ^ k a := by
          funext z
          simp only [f, smul_eq_mul]
          ring
        rw [hfun, contourIntegral_smul, contourIntegral_pow_eq_zero,
          smul_zero]
      have hfun :
          (fun z : ℂ => ∑ j ∈ insert a s, z ^ k j * c j) =
            fun z => f z + g z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hfun, contourIntegral_add hf hg, hterm, ih, zero_add]
end

set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    contourIntegral (fun z => Polynomial.eval z p) Omega.boundaryParam = 0 := by
  have hfun :
      (fun z : ℂ => Polynomial.eval z p) =
        fun z => ∑ i ∈ Finset.range (p.natDegree + 1),
          z ^ i * p.coeff i := by
    funext z
    rw [Polynomial.eval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun]
  exact contourIntegral_finset_sum_pow_mul_eq_zero
    Omega (Finset.range (p.natDegree + 1)) id p.coeff
