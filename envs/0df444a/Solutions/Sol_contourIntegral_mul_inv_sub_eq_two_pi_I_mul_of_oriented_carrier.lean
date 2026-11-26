-- Prove2me | solution 1 for contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_oriented_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:42.380335+00:00
-- url     : https://prove2.me/submissions/8678beaf-4629-478e-8c72-e0bce7a326a1

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Theorems.Thm_contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_kernel_eq_one
import Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology
theorem _root_.solution
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    contourIntegral (fun sigma => f sigma * (sigma - z)⁻¹)
        Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) * f z := by
  apply contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_kernel_eq_one
    Omega hf hz
  exact crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
    Omega c hc hcside z hz
