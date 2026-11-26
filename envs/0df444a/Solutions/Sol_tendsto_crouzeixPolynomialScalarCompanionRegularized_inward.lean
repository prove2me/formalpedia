-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanionRegularized_inward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:23.775906+00:00
-- url     : https://prove2.me/submissions/93eb178d-ba09-4409-8a3c-1071710c4e9f

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_smoothJordanInwardPoint_mem_carrier
import Theorems.Thm_exists_norm_inward_regularized_integrand_sub_le
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
import Theorems.Thm_contourIntegral_sub
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun r : ℝ ↦ crouzeixPolynomialScalarCompanionRegularized
        Omega p xi (smoothJordanInwardPoint c xi r))
      (nhdsWithin 0 (Ioc (0 : ℝ) 1))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  let l : Filter ℝ := nhdsWithin 0 (Ioc (0 : ℝ) 1)
  let q := p /ₘ (Polynomial.X - Polynomial.C xi)
  let N : ℂ → ℂ := fun sigma ↦
    star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)
  let D : ℝ → ℝ → ℂ := fun r t ↦
    deriv Omega.boundaryParam t •
      ((N (Omega.boundaryParam t) *
          (Omega.boundaryParam t - smoothJordanInwardPoint c xi r)⁻¹) -
        (N (Omega.boundaryParam t) *
          (Omega.boundaryParam t - xi)⁻¹))
  obtain ⟨C, hC, hdom⟩ :=
    exists_norm_inward_regularized_integrand_sub_le Omega p hc hxi
  let bound : ℝ → ℝ := fun t ↦
    C * (‖deriv Omega.boundaryParam t‖ *
      ‖Polynomial.eval (Omega.boundaryParam t) q‖)
  have hboundCont : Continuous bound := by
    exact continuous_const.mul
      ((Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).norm.mul
        (q.continuous.comp
          Omega.boundaryParam_contDiff.continuous).norm)
  have hboundInt : IntervalIntegrable bound MeasureTheory.volume
      (0 : ℝ) (2 * Real.pi) := hboundCont.intervalIntegrable _ _
  have hselfInt :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
      Omega p xi
  have hDmeas : ∀ᶠ r in l,
      AEStronglyMeasurable (D r)
        (MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hz : smoothJordanInwardPoint c xi r ∈ Omega.carrier :=
      smoothJordanInwardPoint_mem_carrier Omega hc hxi hr
    have hne : ∀ t : ℝ,
        Omega.boundaryParam t - smoothJordanInwardPoint c xi r ≠ 0 := by
      intro t
      apply sub_ne_zero.mpr
      intro heq
      have hsigma : Omega.boundaryParam t ∈ frontier Omega.carrier := by
        rw [← Omega.boundaryParam_range]
        exact mem_range_self t
      have hsigmaCarrier : Omega.boundaryParam t ∈ Omega.carrier := heq ▸ hz
      have hempty : Omega.boundaryParam t ∈ (∅ : Set ℂ) := by
        rw [← Omega.isOpen_carrier.inter_frontier_eq]
        exact ⟨hsigmaCarrier, hsigma⟩
      exact hempty
    have hden : Continuous (fun t : ℝ ↦
        Omega.boundaryParam t - smoothJordanInwardPoint c xi r) :=
      Omega.boundaryParam_contDiff.continuous.sub continuous_const
    have hfirst : StronglyMeasurable (fun t : ℝ ↦
        deriv Omega.boundaryParam t •
          (N (Omega.boundaryParam t) *
            (Omega.boundaryParam t -
              smoothJordanInwardPoint c xi r)⁻¹)) := by
      apply Continuous.stronglyMeasurable
      exact
        (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).smul
          ((((p.continuous.comp
              Omega.boundaryParam_contDiff.continuous).star.sub
                continuous_const).mul (hden.inv₀ hne)))
    have hselfMeas : AEStronglyMeasurable
        (fun t : ℝ ↦ deriv Omega.boundaryParam t •
          (N (Omega.boundaryParam t) *
            (Omega.boundaryParam t - xi)⁻¹))
        (MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
      change IntervalIntegrable
          (fun t : ℝ ↦ deriv Omega.boundaryParam t •
            ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval xi p)) *
              (Omega.boundaryParam t - xi)⁻¹))
          MeasureTheory.volume (0 : ℝ) (2 * Real.pi) at hselfInt
      exact hselfInt.def'.aestronglyMeasurable
    have heq : D r =
        (fun t : ℝ ↦ deriv Omega.boundaryParam t •
          (N (Omega.boundaryParam t) *
            (Omega.boundaryParam t -
              smoothJordanInwardPoint c xi r)⁻¹)) -
        fun t : ℝ ↦ deriv Omega.boundaryParam t •
          (N (Omega.boundaryParam t) *
            (Omega.boundaryParam t - xi)⁻¹) := by
      funext t
      simp only [D, Pi.sub_apply, smul_sub]
    rw [heq]
    exact hfirst.aestronglyMeasurable.sub hselfMeas
  have hDbound : ∀ᶠ r in l,
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        ‖D r t‖ ≤ bound t := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards with t
    intro ht
    have ht' := uIoc_subset_uIcc ht
    rw [uIcc_of_le Real.two_pi_pos.le] at ht'
    exact hdom r hr t ht'
  have hDlim : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        Filter.Tendsto (fun r ↦ D r t) l (nhds 0) := by
    filter_upwards with t
    intro _ht
    let sigma := Omega.boundaryParam t
    by_cases hsigma : sigma = xi
    · have hzero : (fun r ↦ D r t) = fun _ ↦ 0 := by
        funext r
        dsimp only [D, N, sigma] at hsigma ⊢
        rw [hsigma]
        simp only [sub_self, inv_zero, mul_zero, zero_mul, sub_self, smul_zero]
      rw [hzero]
      exact tendsto_const_nhds
    · have hzcont : Continuous (smoothJordanInwardPoint c xi) := by
        unfold smoothJordanInwardPoint
        fun_prop
      have hden : ContinuousAt
          (fun r : ℝ ↦ sigma - smoothJordanInwardPoint c xi r) 0 :=
        continuousAt_const.sub hzcont.continuousAt
      have hden0 : sigma - smoothJordanInwardPoint c xi 0 ≠ 0 := by
        simpa only [smoothJordanInwardPoint, sub_zero, one_smul, zero_smul,
          add_zero] using sub_ne_zero.mpr hsigma
      have hinv := hden.inv₀ hden0
      have hmul : ContinuousAt
          (fun r : ℝ ↦ N sigma *
            (sigma - smoothJordanInwardPoint c xi r)⁻¹) 0 :=
        continuousAt_const.mul hinv
      have hsecond : ContinuousAt
          (fun _ : ℝ ↦ N sigma * (sigma - xi)⁻¹) 0 :=
        continuousAt_const
      have hcont : ContinuousAt (fun r ↦ D r t) 0 := by
        change ContinuousAt
          (fun r : ℝ ↦ deriv Omega.boundaryParam t •
            (N sigma * (sigma - smoothJordanInwardPoint c xi r)⁻¹ -
              N sigma * (sigma - xi)⁻¹)) 0
        have hderiv : ContinuousAt
            (fun _ : ℝ ↦ deriv Omega.boundaryParam t) 0 :=
          continuousAt_const
        exact hderiv.smul (hmul.sub hsecond)
      have hl : l ≤ nhds (0 : ℝ) := by
        dsimp only [l, nhdsWithin]
        exact inf_le_left
      have htend := hcont.tendsto.mono_left hl
      simpa only [l, D, smoothJordanInwardPoint, sub_zero, one_smul,
        zero_smul, add_zero, sub_self, smul_zero] using htend
  have hDIntegral : Filter.Tendsto
      (fun r ↦ ∫ t in (0 : ℝ)..(2 * Real.pi), D r t)
      l (nhds 0) := by
    have h :=
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        bound hDmeas hDbound hboundInt hDlim
    simpa only [intervalIntegral.integral_zero] using h
  rw [← tendsto_sub_nhds_zero_iff]
  have hscaled : Filter.Tendsto
      (fun r ↦ (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), D r t)
      l (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hDIntegral
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hz : smoothJordanInwardPoint c xi r ∈ Omega.carrier :=
    smoothJordanInwardPoint_mem_carrier Omega hc hxi hr
  have hzfrontier : smoothJordanInwardPoint c xi r ∉
      frontier Omega.carrier := by
    intro hzfrontier
    have hempty : smoothJordanInwardPoint c xi r ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact hempty
  have hfirst : ContourIntegrable
      (fun sigma ↦ N sigma *
        (sigma - smoothJordanInwardPoint c xi r)⁻¹)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · have hden : ContinuousOn
          (fun sigma : ℂ ↦
            sigma - smoothJordanInwardPoint c xi r)
          (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) :=
        continuous_id.continuousOn.sub continuous_const.continuousOn
      have hne : ∀ sigma ∈
          Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi),
          sigma - smoothJordanInwardPoint c xi r ≠ 0 := by
        rintro sigma ⟨t, _ht, rfl⟩ hzero
        apply hzfrontier
        have heq := sub_eq_zero.mp hzero
        rw [← heq, ← Omega.boundaryParam_range]
        exact mem_range_self t
      exact ((p.continuous.star.continuousOn.sub
        continuous_const.continuousOn).mul (hden.inv₀ hne))
  have hself : ContourIntegrable
      (fun sigma ↦ N sigma * (sigma - xi)⁻¹)
      Omega.boundaryParam := by
    exact
      contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
        Omega p xi
  unfold crouzeixPolynomialScalarCompanionRegularized
  rw [← mul_sub, ← contourIntegral_sub hfirst hself]
  rfl
