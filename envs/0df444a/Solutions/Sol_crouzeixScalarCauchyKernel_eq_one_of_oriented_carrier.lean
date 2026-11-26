-- Prove2me | solution 1 for crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:43.807855+00:00
-- url     : https://prove2.me/submissions/bd863136-89e3-4808-912a-6babaf88d2a7

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier_point
import Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_basepoint


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1 := by
  exact crouzeixScalarCauchyKernel_eq_one_of_basepoint Omega c hc
    (crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier_point
      Omega c hc hcside)
