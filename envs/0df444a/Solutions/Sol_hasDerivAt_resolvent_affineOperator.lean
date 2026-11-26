-- Prove2me | solution 1 for hasDerivAt_resolvent_affineOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:31.524508+00:00
-- url     : https://prove2.me/submissions/c9b97926-a651-471f-9a1e-5774f54acb78

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (B D : E →L[ℂ] E) (s z : ℂ)
    (hres : z ∈ resolventSet ℂ (B + s • D)) :
    HasDerivAt (fun w : ℂ => resolvent (B + w • D) z)
      (resolvent (B + s • D) z * D * resolvent (B + s • D) z) s := by
  have hpath : HasDerivAt (fun w : ℂ => B + w • D) D s := by
    convert!
      (hasDerivAt_const s B).add ((hasDerivAt_id s).smul_const D) using 1
    simp only [zero_add, one_smul]
  simpa only [Function.comp_apply, ContinuousLinearMap.mulLeftRight_apply] using!
    (spectrum.hasFDerivAt_resolvent hres).comp_hasDerivAt s hpath
