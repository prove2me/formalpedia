-- Prove2me | solution 1 for crouzeixProductRemainderPolynomial_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:40:41.378373+00:00
-- url     : https://prove2.me/submissions/d5766720-32cb-4958-a135-69127fb2a549

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_contourIntegral_smul
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    crouzeixProductRemainderPolynomial Omega (a • p) =
      (star a * a) • crouzeixProductRemainderPolynomial Omega p := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_smul, star_zero, zero_mul,
      crouzeixProductRemainderPolynomial, Polynomial.natDegree_zero,
      Finset.range_zero, Finset.sum_empty]
  have hcoeff (z : ℂ) (i : ℕ) :
      ((a • p) /ₘ (Polynomial.X - Polynomial.C z)).coeff i =
        a * (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i := by
    rw [Polynomial.coeff_divByMonic_X_sub_C, Polynomial.coeff_divByMonic_X_sub_C]
    rw [Polynomial.natDegree_smul p ha]
    simp only [Polynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hintegral (i : ℕ) :
      contourIntegral
          (fun z => star (Polynomial.eval z (a • p)) *
            ((a • p) /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam =
        (star a * a) *
          contourIntegral
            (fun z => star (Polynomial.eval z p) *
              (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
            Omega.boundaryParam := by
    have hfun :
        (fun z => star (Polynomial.eval z (a • p)) *
          ((a • p) /ₘ (Polynomial.X - Polynomial.C z)).coeff i) =
        fun z => (star a * a) •
          (star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) := by
      funext z
      rw [Polynomial.eval_smul, hcoeff]
      simp only [smul_eq_mul, star_mul]
      ring
    rw [hfun, contourIntegral_smul]
    simp only [smul_eq_mul]
  unfold crouzeixProductRemainderPolynomial
  rw [Finset.smul_sum]
  apply Finset.sum_congr
  · rw [Polynomial.natDegree_smul p ha]
  · intro i hi
    rw [hintegral]
    simp only [Polynomial.smul_monomial]
    congr 1
    ring
