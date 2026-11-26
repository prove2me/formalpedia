-- Prove2me | solution 1 for contourIntegral_crouzeixProductRemainder_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:57.789496+00:00
-- url     : https://prove2.me/submissions/43fe70e6-4465-4623-9bce-f53eeeefbf74

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_continuous_coeff_divByMonic_X_sub_C
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    contourIntegral
        (fun z => star (Polynomial.eval z p) •
          Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
        Omega.boundaryParam =
      ∑ i ∈ Finset.range p.natDegree,
        contourIntegral
          (fun z => star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam • A ^ i := by
  by_cases hp : p.natDegree = 0
  · have hqzero : ∀ z : ℂ, p /ₘ (Polynomial.X - Polynomial.C z) = 0 := by
      intro z
      ext i
      rw [Polynomial.coeff_divByMonic_X_sub_C, hp]
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp only [coeff_zero]
    simp only [hqzero, map_zero, smul_zero, contourIntegral, intervalIntegral.integral_zero,
      hp, Finset.range_zero, Finset.sum_empty]
  · have hdegree (z : ℂ) :
        (p /ₘ (Polynomial.X - Polynomial.C z)).natDegree < p.natDegree := by
      rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C z),
        Polynomial.natDegree_X_sub_C]
      omega
    have hfun :
        (fun z => star (Polynomial.eval z p) •
          Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z))) =
        fun z => ∑ i ∈ Finset.range p.natDegree,
          (star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) • A ^ i := by
      funext z
      rw [Polynomial.aeval_eq_sum_range' (hdegree z) A]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul]
    rw [hfun]
    unfold contourIntegral
    simp only [Finset.smul_sum, smul_smul]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [intervalIntegral.integral_smul_const, smul_eq_mul]
    · intro i hi
      have hcontinuous : Continuous (fun z : ℂ =>
          star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) :=
        p.continuous.star.mul (continuous_coeff_divByMonic_X_sub_C p i)
      have hcontour : ContourIntegrable
          (fun z => (star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) • A ^ i)
          Omega.boundaryParam := by
        apply ContourIntegrable.of_continuousOn
        · exact Omega.boundaryParam_contDiff.continuous.continuousOn
        · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
        · exact (hcontinuous.smul continuous_const).continuousOn
      simpa only [ContourIntegrable, smul_smul, smul_eq_mul] using hcontour
