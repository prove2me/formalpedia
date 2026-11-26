-- Prove2me | solution 1 for contourIntegral_aeval_divByMonic_X_sub_C_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:31.707213+00:00
-- url     : https://prove2.me/submissions/4bb4bd86-ea3f-45cd-80bc-6b2d58552aec

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_contourIntegral_add
import Theorems.Thm_contourIntegral_eq_zero_of_hasDerivAt_of_closed
import Theorems.Thm_contourIntegral_smul
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange


section
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem contourIntegral_pow_eq_zero_polynomialCauchy
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
        (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
    · exact (continuous_pow n).continuousOn
  · simpa only [zero_add] using Omega.boundaryParam_periodic 0
private theorem contourIntegral_finset_sum_pow_mul_eq_zero_polynomialCauchy
    (Omega : SmoothJordanDomain) (s : Finset ℕ) (k : ℕ → ℕ) (c : ℕ → ℂ) :
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
            (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
        · exact ((continuous_pow (k a)).mul continuous_const).continuousOn
      have hg : ContourIntegrable g Omega.boundaryParam := by
        apply ContourIntegrable.of_continuousOn
        · exact Omega.boundaryParam_contDiff.continuous.continuousOn
        · exact
            (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
        · exact (continuous_finsetSum s fun j _ =>
            (continuous_pow (k j)).mul continuous_const).continuousOn
      have hterm : contourIntegral f Omega.boundaryParam = 0 := by
        have hfun : f = fun z => c a • z ^ k a := by
          funext z
          simp only [f, smul_eq_mul]
          ring
        rw [hfun, contourIntegral_smul,
          contourIntegral_pow_eq_zero_polynomialCauchy, smul_zero]
      have hfun :
          (fun z : ℂ => ∑ j ∈ insert a s, z ^ k j * c j) =
            fun z => f z + g z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hfun, contourIntegral_add hf hg, hterm, ih, zero_add]
end

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    contourIntegral
        (fun z => Polynomial.aeval A
          (p /ₘ (Polynomial.X - Polynomial.C z)))
        Omega.boundaryParam = 0 := by
  have hfun :
      (fun z : ℂ => Polynomial.aeval A
        (p /ₘ (Polynomial.X - Polynomial.C z))) =
      fun z => ∑ i ∈ Finset.range (p.natDegree + 1),
        (∑ j ∈ Finset.Icc (i + 1) p.natDegree,
          z ^ (j - (i + 1)) * p.coeff j) • A ^ i := by
    funext z
    rw [Polynomial.aeval_eq_sum_range' (x := A) (n := p.natDegree + 1)]
    · congr 1 with i
      rw [Polynomial.coeff_divByMonic_X_sub_C]
    · rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C z),
        Polynomial.natDegree_X_sub_C]
      omega
  rw [hfun]
  unfold contourIntegral
  simp only [Finset.smul_sum, smul_smul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [intervalIntegral.integral_smul_const]
    have hzero :=
      contourIntegral_finset_sum_pow_mul_eq_zero_polynomialCauchy
        Omega (Finset.Icc (i + 1) p.natDegree)
          (fun j => j - (i + 1)) (fun j => p.coeff j)
    unfold contourIntegral at hzero
    have hzero' := congrArg (fun c : ℂ => c • A ^ i) hzero
    simpa only [smul_eq_mul, zero_smul] using hzero'
  · intro i _
    have hcontour : ContourIntegrable
        (fun z => (∑ j ∈ Finset.Icc (i + 1) p.natDegree,
          z ^ (j - (i + 1)) * p.coeff j) • A ^ i)
        Omega.boundaryParam := by
      apply ContourIntegrable.of_continuousOn
      · exact Omega.boundaryParam_contDiff.continuous.continuousOn
      · exact
          (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
      · exact (continuous_finsetSum (Finset.Icc (i + 1) p.natDegree) fun j _ =>
          (continuous_pow (j - (i + 1))).mul continuous_const).smul
            continuous_const |>.continuousOn
    simpa only [ContourIntegrable, smul_smul, smul_eq_mul] using hcontour
