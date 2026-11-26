-- Prove2me | solution 1 for contourIntegral_inv_sub_mul_eq_two_pi_I_mul_of_kernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:22.537821+00:00
-- url     : https://prove2.me/submissions/65f5b150-ff4e-4c18-a39b-8ecab62f3a5e

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Theorems.Thm_contourIntegral_inv_sub_mul_eq_contourIntegral_inv_sub_mul_value

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology
theorem _root_.solution
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier) {z : ℂ}
    (hz : z ∈ Omega.carrier)
    (hkernel : crouzeixScalarCauchyKernel Omega z = 1) :
    contourIntegral (fun sigma => (sigma - z)⁻¹ * f sigma)
        Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) * f z := by
  rw [contourIntegral_inv_sub_mul_eq_contourIntegral_inv_sub_mul_value
    Omega hf hz]
  have hq : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  have hmass : contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
      Omega.boundaryParam = 2 * (Real.pi : ℂ) * I := by
    calc
      contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
          Omega.boundaryParam =
          (2 * (Real.pi : ℂ) * I) *
            ((2 * (Real.pi : ℂ) * I)⁻¹ *
              contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
                Omega.boundaryParam) := by
            field_simp [Real.pi_ne_zero, I_ne_zero]
      _ = (2 * (Real.pi : ℂ) * I) *
          crouzeixScalarCauchyKernel Omega z := by
            rfl
      _ = 2 * (Real.pi : ℂ) * I := by
            rw [hkernel, mul_one]
  rw [hmass]
