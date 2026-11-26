-- Prove2me | solution 1 for crouzeixScalarCauchyKernel_eq_one_of_basepoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:54.993142+00:00
-- url     : https://prove2.me/submissions/faaab4e0-584f-4160-ade6-40d89e27c893

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Theorems.Thm_crouzeixScalarCauchyKernel_eq_of_mem_carrier

set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hkc : crouzeixScalarCauchyKernel Omega c = 1) :
    ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1 := by
  intro z hz
  exact (crouzeixScalarCauchyKernel_eq_of_mem_carrier
    Omega hz hc).trans hkc
