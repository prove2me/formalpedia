-- Prove2me | solution 1 for crouzeixScalarCauchyKernel_eq_zero_of_not_mem_closure_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:54.798667+00:00
-- url     : https://prove2.me/submissions/a0efed30-f964-46bf-8ad7-a61d966a481f

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Theorems.Thm_contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier

set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) {z : ℂ}
    (hz : z ∉ closure Omega.carrier) :
    crouzeixScalarCauchyKernel Omega z = 0 := by
  unfold crouzeixScalarCauchyKernel
  rw [contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier
    Omega hz, mul_zero]
