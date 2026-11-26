-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_eq_norm_auxiliaryOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:26.524883+00:00
-- url     : https://prove2.me/submissions/2a88dc4e-0659-4a4e-af40-ee3ba436a127

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange


attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
section
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
private theorem norm_apply_one_eq_norm_complex_endomorphism
    (T : ℂ →L[ℂ] ℂ) : ‖T 1‖ = ‖T‖ := by
  have hT : T = ContinuousLinearMap.toSpanSingleton ℂ (T 1) := by
    apply ContinuousLinearMap.ext
    intro x
    change T x = x * T 1
    calc
      T x = T (x • (1 : ℂ)) := by simp only [smul_eq_mul, mul_one]
      _ = x • T 1 := map_smul T x 1
      _ = x * T 1 := by rfl
  rw [hT, ContinuousLinearMap.norm_toSpanSingleton]
  change ‖(1 : ℂ) * T 1‖ = ‖T 1‖
  rw [one_mul]
end

set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ =
      ‖crouzeixPolynomialAuxiliaryOperator
        (ContinuousLinearMap.toSpanSingleton ℂ z) Omega p‖ := by
  rw [crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one
    Omega p hz]
  exact norm_apply_one_eq_norm_complex_endomorphism _
