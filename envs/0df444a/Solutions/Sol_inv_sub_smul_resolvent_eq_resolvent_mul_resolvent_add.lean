-- Prove2me | solution 1 for inv_sub_smul_resolvent_eq_resolvent_mul_resolvent_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:00.440807+00:00
-- url     : https://prove2.me/submissions/6479f687-7c55-4cfe-becc-a2181dd49b60

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_resolvent_sub_smul_one_shift
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {z sigma : ℂ}
    (hz : z ∈ resolventSet ℂ A) (hsigma : sigma ∈ resolventSet ℂ A)
    (hne : z ≠ sigma) :
    (sigma - z)⁻¹ • resolvent A z =
      resolvent A z * resolvent A sigma +
        (sigma - z)⁻¹ • resolvent A sigma := by
  let B : E →L[ℂ] E := A - (sigma - z) • (1 : E →L[ℂ] E)
  have hB : z ∈ resolventSet ℂ B := by
    rw [mem_resolventSet_iff] at hsigma ⊢
    have heq : algebraMap ℂ (E →L[ℂ] E) z - B =
        algebraMap ℂ (E →L[ℂ] E) sigma - A := by
      dsimp only [B]
      simp only [Algebra.algebraMap_eq_smul_one]
      module
    rwa [heq]
  have hresB : resolvent B z = resolvent A sigma := by
    dsimp only [B]
    rw [resolvent_sub_smul_one_shift]
    congr 1
    ring
  have hsecond := spectrum.resolvent_sub_resolvent hz hB
  rw [hresB] at hsecond
  have hdiff : resolvent A z - resolvent A sigma =
      (sigma - z) • (resolvent A z * resolvent A sigma) := by
    calc
      resolvent A z - resolvent A sigma =
          resolvent A z * (A - B) * resolvent A sigma := hsecond
      _ = (sigma - z) • (resolvent A z * resolvent A sigma) := by
        dsimp only [B]
        simp only [sub_sub_cancel, mul_smul_comm, mul_one, smul_mul_assoc]
  have hscaled := congrArg (fun T : E →L[ℂ] E => (sigma - z)⁻¹ • T) hdiff
  simp only [smul_sub, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm), one_smul] at hscaled
  exact sub_eq_iff_eq_add.mp hscaled
