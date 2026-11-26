-- Prove2me | solution 1 for crouzeixScalarCauchyKernel_eq_of_mem_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:07.856005+00:00
-- url     : https://prove2.me/submissions/715bf84b-9070-4c91-be32-18f92532e10f

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_C_one_eq_zero_of_mem_carrier
import Theorems.Thm_analyticOn_crouzeixPolynomialScalarCompanion
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_hasDerivAt_crouzeixPolynomialScalarCompanion
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) {z w : ℂ}
    (hz : z ∈ Omega.carrier) (hw : w ∈ Omega.carrier) :
    crouzeixScalarCauchyKernel Omega z =
      crouzeixScalarCauchyKernel Omega w := by
  let f : ℂ → ℂ :=
    crouzeixPolynomialScalarCompanion Omega (Polynomial.C 1)
  have hf : DifferentiableOn ℂ f Omega.carrier := by
    exact (analyticOn_crouzeixPolynomialScalarCompanion
      Omega (Polynomial.C 1)).differentiableOn
  have hfzero : EqOn (deriv f) 0 Omega.carrier := by
    intro x hx
    rw [Pi.zero_apply]
    have hderiv := (hasDerivAt_crouzeixPolynomialScalarCompanion
      Omega (Polynomial.C 1) hx).deriv
    dsimp only [f] at hderiv ⊢
    rw [hderiv,
      crouzeixPolynomialScalarCompanionDeriv_C_one_eq_zero_of_mem_carrier
        Omega hx]
  have heq := Omega.isOpen_carrier.is_const_of_deriv_eq_zero
    Omega.strictConvex_carrier.convex.isPreconnected hf hfzero hz hw
  simpa only [f, crouzeixPolynomialScalarCompanion,
    crouzeixScalarCauchyKernel, Polynomial.eval_C, star_one, one_mul] using heq
