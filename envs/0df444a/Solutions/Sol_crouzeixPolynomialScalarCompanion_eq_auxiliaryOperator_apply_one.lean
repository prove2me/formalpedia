-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:25.692882+00:00
-- url     : https://prove2.me/submissions/25a108cd-9494-48d9-ac69-83689f155c63

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_ContinuousLinearMap_contourIntegral_comp_comm
import Theorems.Thm_crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange


attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
section
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
private theorem resolvent_toSpanSingleton_apply_one_eq_inv (z sigma : ℂ)
    (hne : sigma ≠ z) :
    resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma (1 : ℂ) =
      (sigma - z)⁻¹ := by
  have hsub : (sigma • (1 : ℂ →L[ℂ] ℂ) -
      ContinuousLinearMap.toSpanSingleton ℂ z) =
      ContinuousLinearMap.toSpanSingleton ℂ (sigma - z) := by
    apply ContinuousLinearMap.ext
    intro x
    change sigma * x - x * z = x * (sigma - z)
    ring
  have hunit : IsUnit (sigma • (1 : ℂ →L[ℂ] ℂ) -
      ContinuousLinearMap.toSpanSingleton ℂ z) := by
    rw [hsub]
    let u : (ℂ →L[ℂ] ℂ)ˣ :=
      { val := ContinuousLinearMap.toSpanSingleton ℂ (sigma - z)
        inv := ContinuousLinearMap.toSpanSingleton ℂ (sigma - z)⁻¹
        val_inv := by
          apply ContinuousLinearMap.ext
          intro x
          change (x * (sigma - z)⁻¹) * (sigma - z) = x
          field_simp
        inv_val := by
          apply ContinuousLinearMap.ext
          intro x
          change (x * (sigma - z)) * (sigma - z)⁻¹ = x
          field_simp }
    exact ⟨u, rfl⟩
  have hsigma : sigma ∈ resolventSet ℂ
      (ContinuousLinearMap.toSpanSingleton ℂ z) := by
    rw [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]
    exact hunit
  have hmul :
      (sigma • (1 : ℂ →L[ℂ] ℂ) -
          ContinuousLinearMap.toSpanSingleton ℂ z) *
        resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma = 1 := by
    have hunitEq : sigma • (1 : ℂ →L[ℂ] ℂ) -
        ContinuousLinearMap.toSpanSingleton ℂ z =
          (hsigma.unit : ℂ →L[ℂ] ℂ) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hsigma.unit_spec.symm
    calc
      (sigma • (1 : ℂ →L[ℂ] ℂ) -
            ContinuousLinearMap.toSpanSingleton ℂ z) *
          resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma =
          (hsigma.unit : ℂ →L[ℂ] ℂ) *
            (↑((hsigma.unit)⁻¹) : ℂ →L[ℂ] ℂ) := by
        rw [hunitEq, spectrum.resolvent_eq hsigma]
      _ = 1 := Units.mul_inv _
  have hx := congrArg (fun T : ℂ →L[ℂ] ℂ ↦ T (1 : ℂ)) hmul
  have hx' : 1 = sigma *
      (resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma 1) -
        (resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma 1) * z := by
    change sigma *
        (resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma 1) -
          (resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma 1) * z =
      1 at hx
    exact hx.symm
  let y := resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma 1
  have hmul : y * (sigma - z) = 1 := by
    calc
      y * (sigma - z) = sigma * y - y * z := by ring
      _ = 1 := hx'.symm
  calc
    y = y * ((sigma - z) * (sigma - z)⁻¹) := by
      rw [mul_inv_cancel₀ (sub_ne_zero.mpr hne), mul_one]
    _ = (y * (sigma - z)) * (sigma - z)⁻¹ := by ring
    _ = (sigma - z)⁻¹ := by rw [hmul, one_mul]
end

set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega p z =
      crouzeixPolynomialAuxiliaryOperator
        (ContinuousLinearMap.toSpanSingleton ℂ z) Omega p 1 := by
  let A : ℂ →L[ℂ] ℂ := ContinuousLinearMap.toSpanSingleton ℂ z
  have hAeq : A = z • (1 : ℂ →L[ℂ] ℂ) := by
    apply ContinuousLinearMap.ext
    intro x
    change x * z = z * x
    ring
  have hW : closure (numericalRange A) ⊆ Omega.carrier := by
    have hnr : numericalRange A ⊆ ({z} : Set ℂ) := by
      rintro w ⟨x, hx, rfl⟩
      rw [hAeq]
      simp only [smul_apply, one_apply_eq_self, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hx]
      norm_num
    exact (closure_minimal hnr isClosed_singleton).trans (by
      intro w hw
      simpa only [mem_singleton_iff] using hw ▸ hz)
  have hint := crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable
    A Omega p hW
  let L : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
  have hLcontour :
      contourIntegral
          (fun sigma ↦ L (star (Polynomial.eval sigma p) • resolvent A sigma))
          Omega.boundaryParam =
        L (contourIntegral
          (fun sigma ↦ star (Polynomial.eval sigma p) • resolvent A sigma)
          Omega.boundaryParam) :=
    L.contourIntegral_comp_comm hint
  have hscalarContour :
      contourIntegral
          (fun sigma ↦ star (Polynomial.eval sigma p) * (sigma - z)⁻¹)
          Omega.boundaryParam =
        contourIntegral
          (fun sigma ↦ L (star (Polynomial.eval sigma p) • resolvent A sigma))
          Omega.boundaryParam := by
    unfold contourIntegral
    apply intervalIntegral.integral_congr
    intro t _ht
    have hne : Omega.boundaryParam t ≠ z := by
      intro heq
      have hzfrontier : z ∈ frontier Omega.carrier := by
        rw [← heq, ← Omega.boundaryParam_range]
        exact mem_range_self t
      have hempty : z ∈ (∅ : Set ℂ) := by
        rw [← Omega.isOpen_carrier.inter_frontier_eq]
        exact ⟨hz, hzfrontier⟩
      exact hempty
    change deriv Omega.boundaryParam t *
        (star (Polynomial.eval (Omega.boundaryParam t) p) *
          (Omega.boundaryParam t - z)⁻¹) =
      deriv Omega.boundaryParam t *
        L (star (Polynomial.eval (Omega.boundaryParam t) p) •
          resolvent A (Omega.boundaryParam t))
    congr 1
    change star (Polynomial.eval (Omega.boundaryParam t) p) *
        (Omega.boundaryParam t - z)⁻¹ =
      star (Polynomial.eval (Omega.boundaryParam t) p) *
        resolvent A (Omega.boundaryParam t) 1
    rw [resolvent_toSpanSingleton_apply_one_eq_inv z
      (Omega.boundaryParam t) hne]
  calc
    crouzeixPolynomialScalarCompanion Omega p z =
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          contourIntegral
            (fun sigma ↦ star (Polynomial.eval sigma p) * (sigma - z)⁻¹)
            Omega.boundaryParam := rfl
    _ = (2 * (Real.pi : ℂ) * I)⁻¹ *
        L (contourIntegral
          (fun sigma ↦ star (Polynomial.eval sigma p) • resolvent A sigma)
          Omega.boundaryParam) := by rw [hscalarContour, hLcontour]
    _ = (crouzeixPolynomialAuxiliaryOperator A Omega p) 1 := by rfl
