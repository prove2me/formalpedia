-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_sub_self_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:01:25.189441+00:00
-- url     : https://prove2.me/submissions/2899b2ba-3fb0-40ab-bdd7-9ca75eed9445

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_ae_boundaryParam_ne_of_mem_frontier
import Theorems.Thm_smoothJordanInwardPoint_mem_carrier
import Theorems.Thm_exists_uniform_norm_inward_regularized_integrand_sub_le_deriv
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
      (fun x : ℝ × ℂ =>
        crouzeixPolynomialScalarCompanionRegularized Omega p x.2
            (smoothJordanInwardPoint c x.2 x.1) -
          crouzeixPolynomialScalarCompanionRegularized Omega p x.2 x.2)
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))
      (nhds 0) := by
  let l : Filter (ℝ × ℂ) := nhdsWithin (0, xi)
    (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier)
  let N : ℂ → ℂ → ℂ := fun eta sigma =>
    star (Polynomial.eval sigma p) - star (Polynomial.eval eta p)
  let D : (ℝ × ℂ) → ℝ → ℂ := fun x t =>
    deriv Omega.boundaryParam t •
      ((N x.2 (Omega.boundaryParam t) *
          (Omega.boundaryParam t -
            smoothJordanInwardPoint c x.2 x.1)⁻¹) -
        (N x.2 (Omega.boundaryParam t) *
          (Omega.boundaryParam t - x.2)⁻¹))
  obtain ⟨C, hC, hdom⟩ :=
    exists_uniform_norm_inward_regularized_integrand_sub_le_deriv
      Omega p hc
  let bound : ℝ → ℝ := fun t => C * ‖deriv Omega.boundaryParam t‖
  have hboundCont : Continuous bound :=
    continuous_const.mul
      (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).norm
  have hboundInt : IntervalIntegrable bound MeasureTheory.volume
      (0 : ℝ) (2 * Real.pi) := hboundCont.intervalIntegrable _ _
  have hDmeas : ∀ᶠ x in l,
      AEStronglyMeasurable (D x)
        (MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hz : smoothJordanInwardPoint c x.2 x.1 ∈ Omega.carrier :=
      smoothJordanInwardPoint_mem_carrier Omega hc hx.2 hx.1
    have hne : ∀ t : ℝ,
        Omega.boundaryParam t -
          smoothJordanInwardPoint c x.2 x.1 ≠ 0 := by
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
    have hden : Continuous (fun t : ℝ =>
        Omega.boundaryParam t - smoothJordanInwardPoint c x.2 x.1) :=
      Omega.boundaryParam_contDiff.continuous.sub continuous_const
    have hfirst : StronglyMeasurable (fun t : ℝ =>
        deriv Omega.boundaryParam t •
          (N x.2 (Omega.boundaryParam t) *
            (Omega.boundaryParam t -
              smoothJordanInwardPoint c x.2 x.1)⁻¹)) := by
      apply Continuous.stronglyMeasurable
      exact
        (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).smul
          ((((p.continuous.comp
              Omega.boundaryParam_contDiff.continuous).star.sub
                continuous_const).mul (hden.inv₀ hne)))
    have hselfInt :=
      contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
        Omega p x.2
    have hselfMeas : AEStronglyMeasurable
        (fun t : ℝ => deriv Omega.boundaryParam t •
          (N x.2 (Omega.boundaryParam t) *
            (Omega.boundaryParam t - x.2)⁻¹))
        (MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
      change IntervalIntegrable
          (fun t : ℝ => deriv Omega.boundaryParam t •
            ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval x.2 p)) *
              (Omega.boundaryParam t - x.2)⁻¹))
          MeasureTheory.volume (0 : ℝ) (2 * Real.pi) at hselfInt
      exact hselfInt.def'.aestronglyMeasurable
    have heq : D x =
        (fun t : ℝ => deriv Omega.boundaryParam t •
          (N x.2 (Omega.boundaryParam t) *
            (Omega.boundaryParam t -
              smoothJordanInwardPoint c x.2 x.1)⁻¹)) -
        fun t : ℝ => deriv Omega.boundaryParam t •
          (N x.2 (Omega.boundaryParam t) *
            (Omega.boundaryParam t - x.2)⁻¹) := by
      funext t
      simp only [D, Pi.sub_apply, smul_sub]
    rw [heq]
    exact hfirst.aestronglyMeasurable.sub hselfMeas
  have hDbound : ∀ᶠ x in l,
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        ‖D x t‖ ≤ bound t := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards with t
    intro ht
    have ht' := uIoc_subset_uIcc ht
    rw [uIcc_of_le Real.two_pi_pos.le] at ht'
    exact hdom x.2 hx.2 x.1 hx.1 t ht'
  have hDlim : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        Filter.Tendsto (fun x => D x t) l (nhds 0) := by
    filter_upwards [ae_boundaryParam_ne_of_mem_frontier Omega hxi] with t htne
    intro ht
    let sigma := Omega.boundaryParam t
    have hsigma : sigma ≠ xi := htne ht
    have hzcont : Continuous (fun x : ℝ × ℂ =>
        smoothJordanInwardPoint c x.2 x.1) := by
      unfold smoothJordanInwardPoint
      fun_prop
    have hN : ContinuousAt (fun x : ℝ × ℂ => N x.2 sigma) (0, xi) := by
      dsimp only [N]
      fun_prop
    have hdenFirst : ContinuousAt (fun x : ℝ × ℂ =>
        sigma - smoothJordanInwardPoint c x.2 x.1) (0, xi) :=
      continuousAt_const.sub hzcont.continuousAt
    have hdenFirst0 :
        sigma - smoothJordanInwardPoint c xi 0 ≠ 0 := by
      simpa only [smoothJordanInwardPoint, sub_zero, one_smul, zero_smul,
        add_zero] using sub_ne_zero.mpr hsigma
    have hfirst := hN.mul (hdenFirst.inv₀ hdenFirst0)
    have hdenSelf : ContinuousAt (fun x : ℝ × ℂ => sigma - x.2) (0, xi) := by
      fun_prop
    have hdenSelf0 : sigma - xi ≠ 0 := sub_ne_zero.mpr hsigma
    have hself := hN.mul (hdenSelf.inv₀ hdenSelf0)
    have hcont : ContinuousAt (fun x => D x t) (0, xi) := by
      change ContinuousAt (fun x : ℝ × ℂ =>
        deriv Omega.boundaryParam t •
          (N x.2 sigma *
              (sigma - smoothJordanInwardPoint c x.2 x.1)⁻¹ -
            N x.2 sigma * (sigma - x.2)⁻¹)) (0, xi)
      have hderiv : ContinuousAt
          (fun _ : ℝ × ℂ => deriv Omega.boundaryParam t) (0, xi) :=
        continuousAt_const
      exact hderiv.smul (hfirst.sub hself)
    have hl : l ≤ nhds (0, xi) := by
      dsimp only [l, nhdsWithin]
      exact inf_le_left
    have htend := hcont.tendsto.mono_left hl
    simpa only [l, D, smoothJordanInwardPoint, sub_zero, one_smul,
      zero_smul, add_zero, sub_self, smul_zero] using htend
  have hDIntegral : Filter.Tendsto
      (fun x => ∫ t in (0 : ℝ)..(2 * Real.pi), D x t)
      l (nhds 0) := by
    have h :=
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        bound hDmeas hDbound hboundInt hDlim
    simpa only [intervalIntegral.integral_zero] using h
  have hscaled : Filter.Tendsto
      (fun x => (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), D x t)
      l (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hDIntegral
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hz : smoothJordanInwardPoint c x.2 x.1 ∈ Omega.carrier :=
    smoothJordanInwardPoint_mem_carrier Omega hc hx.2 hx.1
  have hzfrontier : smoothJordanInwardPoint c x.2 x.1 ∉
      frontier Omega.carrier := by
    intro hzfrontier
    have hempty : smoothJordanInwardPoint c x.2 x.1 ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact hempty
  have hfirst : ContourIntegrable
      (fun sigma => N x.2 sigma *
        (sigma - smoothJordanInwardPoint c x.2 x.1)⁻¹)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · have hden : ContinuousOn
          (fun sigma : ℂ =>
            sigma - smoothJordanInwardPoint c x.2 x.1)
          (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) :=
        continuous_id.continuousOn.sub continuous_const.continuousOn
      have hne : ∀ sigma ∈
          Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi),
          sigma - smoothJordanInwardPoint c x.2 x.1 ≠ 0 := by
        rintro sigma ⟨t, _ht, rfl⟩ hzero
        apply hzfrontier
        have heq := sub_eq_zero.mp hzero
        rw [← heq, ← Omega.boundaryParam_range]
        exact mem_range_self t
      exact ((p.continuous.star.continuousOn.sub
        continuous_const.continuousOn).mul (hden.inv₀ hne))
  have hself : ContourIntegrable
      (fun sigma => N x.2 sigma * (sigma - x.2)⁻¹)
      Omega.boundaryParam :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
      Omega p x.2
  unfold crouzeixPolynomialScalarCompanionRegularized
  rw [← mul_sub, ← contourIntegral_sub hfirst hself]
  rfl
