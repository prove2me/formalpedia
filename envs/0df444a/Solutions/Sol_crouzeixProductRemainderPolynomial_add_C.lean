-- Prove2me | solution 1 for crouzeixProductRemainderPolynomial_add_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:21.51024+00:00
-- url     : https://prove2.me/submissions/6825f85f-68cb-4112-af1f-4bb36ac71801

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_continuous_coeff_divByMonic_X_sub_C
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
private theorem contourIntegral_pow_eq_zero
    (Omega : SmoothJordanDomain) (n : ℕ) :
    contourIntegral (fun z : ℂ => z ^ n) Omega.boundaryParam = 0 := by
  apply contourIntegral_eq_zero_of_hasDerivAt_of_closed
    (Fp := fun z : ℂ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
  · intro _ _
    exact (Omega.boundaryParam_contDiff.differentiable (by norm_num)).differentiableAt
  · intro t _
    convert (hasDerivAt_pow (n + 1) (Omega.boundaryParam t)).div_const
      ((n + 1 : ℕ) : ℂ) using 1
    · rfl
    · field_simp
      congr 1
  · apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
    · exact (continuous_pow n).continuousOn
  · simpa only [zero_add] using Omega.boundaryParam_periodic 0
private theorem contourIntegral_finset_sum_pow_mul_eq_zero
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
        · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
        · exact ((continuous_pow (k a)).mul continuous_const).continuousOn
      have hg : ContourIntegrable g Omega.boundaryParam := by
        apply ContourIntegrable.of_continuousOn
        · exact Omega.boundaryParam_contDiff.continuous.continuousOn
        · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
        · exact (continuous_finsetSum s fun j _ =>
            (continuous_pow (k j)).mul continuous_const).continuousOn
      have hterm : contourIntegral f Omega.boundaryParam = 0 := by
        have hfun : f = fun z => c a • z ^ k a := by
          funext z
          simp only [f, smul_eq_mul]
          ring
        rw [hfun, contourIntegral_smul, contourIntegral_pow_eq_zero, smul_zero]
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
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ) :
    crouzeixProductRemainderPolynomial Omega (p + Polynomial.C a) =
      crouzeixProductRemainderPolynomial Omega p := by
  have hquot (z : ℂ) (i : ℕ) :
      ((p + Polynomial.C a) /ₘ (Polynomial.X - Polynomial.C z)).coeff i =
        (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i := by
    rw [Polynomial.coeff_divByMonic_X_sub_C, Polynomial.coeff_divByMonic_X_sub_C,
      Polynomial.natDegree_add_C]
    apply Finset.sum_congr rfl
    intro j hj
    have hjpos : 0 < j := lt_of_lt_of_le (Nat.zero_lt_succ i) (Finset.mem_Icc.mp hj).1
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (Nat.ne_of_gt hjpos), add_zero]
  have hintegral (i : ℕ) :
      contourIntegral
          (fun z => star (Polynomial.eval z (p + Polynomial.C a)) *
            ((p + Polynomial.C a) /ₘ
              (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam =
        contourIntegral
          (fun z => star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam := by
    let f : ℂ → ℂ := fun z => star (Polynomial.eval z p) *
      (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i
    let g : ℂ → ℂ := fun z => star a *
      (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i
    have hf : ContourIntegrable f Omega.boundaryParam := by
      apply ContourIntegrable.of_continuousOn
      · exact Omega.boundaryParam_contDiff.continuous.continuousOn
      · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
      · exact (p.continuous.star.mul
          (continuous_coeff_divByMonic_X_sub_C p i)).continuousOn
    have hg : ContourIntegrable g Omega.boundaryParam := by
      apply ContourIntegrable.of_continuousOn
      · exact Omega.boundaryParam_contDiff.continuous.continuousOn
      · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
      · exact (continuous_const.mul
          (continuous_coeff_divByMonic_X_sub_C p i)).continuousOn
    have hcoeffzero : contourIntegral
        (fun z => (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
        Omega.boundaryParam = 0 := by
      have hfun :
          (fun z => (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) =
            fun z => ∑ j ∈ Finset.Icc (i + 1) p.natDegree,
              z ^ (j - (i + 1)) * p.coeff j := by
        funext z
        rw [Polynomial.coeff_divByMonic_X_sub_C]
      rw [hfun]
      exact contourIntegral_finset_sum_pow_mul_eq_zero Omega _ _ _
    have hgzero : contourIntegral g Omega.boundaryParam = 0 := by
      have hfun : g = fun z => star a •
          (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i := by
        funext z
        simp only [g, smul_eq_mul]
      rw [hfun, contourIntegral_smul, hcoeffzero, smul_zero]
    have hfun :
        (fun z => star (Polynomial.eval z (p + Polynomial.C a)) *
          ((p + Polynomial.C a) /ₘ
            (Polynomial.X - Polynomial.C z)).coeff i) =
          fun z => f z + g z := by
      funext z
      rw [Polynomial.eval_add, Polynomial.eval_C, hquot]
      rw [star_add]
      simp only [f, g]
      ring
    rw [hfun, contourIntegral_add hf hg, hgzero, add_zero]
  unfold crouzeixProductRemainderPolynomial
  rw [Polynomial.natDegree_add_C]
  apply Finset.sum_congr rfl
  intro i _
  rw [hintegral]
