-- Prove2me | solution 1 for re_inner_crouzeixSquareAuxiliaryOperator_nonneg_of_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:27.403736+00:00
-- url     : https://prove2.me/submissions/9680ee5d-69b8-4e3e-944b-1548fea37655

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Theorems.Thm_ContinuousLinearMap_intervalIntegral_smul_add_adjoint
import Theorems.Thm_ContinuousLinearMap_isPositive_intervalIntegral
import Theorems.Thm_crouzeixAuxiliaryIntegrand_contourIntegrable
import Theorems.Thm_isPositive_add_adjoint_smul_resolvent
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange


section
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace SmoothJordanDomain
end SmoothJordanDomain
private theorem intervalIntegrable_boundaryDatum_smul_outwardKernel
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (h : ℂ → ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hh : ContinuousOn h
      (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi))) :
    IntervalIntegrable
      (fun t => h (Omega.boundaryParam t) •
        ((-I * deriv Omega.boundaryParam t) •
          resolvent A (Omega.boundaryParam t)))
      volume 0 (2 * Real.pi) := by
  have hcontour :=
    crouzeixAuxiliaryIntegrand_contourIntegrable A Omega h hOmega hh
  change IntervalIntegrable
    (fun t => deriv Omega.boundaryParam t •
      (h (Omega.boundaryParam t) •
        resolvent A (Omega.boundaryParam t)))
    volume 0 (2 * Real.pi) at hcontour
  have hfun :
      (fun t => h (Omega.boundaryParam t) •
        ((-I * deriv Omega.boundaryParam t) •
          resolvent A (Omega.boundaryParam t))) =
      fun t => (-I) •
        (deriv Omega.boundaryParam t •
          (h (Omega.boundaryParam t) •
            resolvent A (Omega.boundaryParam t))) := by
    funext t
    simp only [smul_smul]
    congr 1
    ring
  rw [hfun]
  exact ⟨hcontour.1.smul_enorm (-I), hcontour.2.smul_enorm (-I)⟩
private theorem intervalIntegrable_adjoint
    {g : ℝ → E →L[ℂ] E} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t => ContinuousLinearMap.adjoint (g t))
      volume a b := by
  let adjointCLM : (E →L[ℂ] E) →L⋆[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap
  change IntervalIntegrable (fun t => adjointCLM (g t)) volume a b
  exact ⟨adjointCLM.integrable_comp hg.1, adjointCLM.integrable_comp hg.2⟩
private theorem intervalIntegrable_smul_add_adjoint
    (B : ℝ → E →L[ℂ] E) (f : ℝ → ℂ) {a b : ℝ}
    (hfB : IntervalIntegrable (fun t => f t • B t) volume a b)
    (hstarfB : IntervalIntegrable (fun t => star (f t) • B t) volume a b) :
    IntervalIntegrable
      (fun t => f t • (B t + ContinuousLinearMap.adjoint (B t)))
      volume a b := by
  have hAdjoint : IntervalIntegrable
      (fun t => ContinuousLinearMap.adjoint (star (f t) • B t))
      volume a b := intervalIntegrable_adjoint hstarfB
  have hfun :
      (fun t => ContinuousLinearMap.adjoint (star (f t) • B t)) =
        fun t => f t • ContinuousLinearMap.adjoint (B t) := by
    funext t
    exact
      (map_smulₛₗ ContinuousLinearMap.adjoint (star (f t)) (B t)).trans (by
        rw [starRingEnd_apply, star_star])
  rw [hfun] at hAdjoint
  simpa only [smul_add] using hfB.add hAdjoint
end

set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0)
    (x : E) :
    0 ≤ RCLike.re ⟪x,
      crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) x⟫_ℂ := by
  let gamma := Omega.boundaryParam
  let f : ℝ → ℂ := fun t =>
    star (Polynomial.eval (gamma t) p) * Polynomial.eval (gamma t) p
  let B : ℝ → E →L[ℂ] E := fun t =>
    (-I * deriv gamma t) • resolvent A (gamma t)
  let K : ℝ → E →L[ℂ] E := fun t =>
    B t + ContinuousLinearMap.adjoint (B t)
  have hfB : IntervalIntegrable (fun t => f t • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) hOmega
        (p.continuous.star.mul p.continuous).continuousOn
  have hstarf : (fun t => star (f t) • B t) = fun t => f t • B t := by
    funext t
    simp only [f, star_mul, star_star]
  have hstarfB : IntervalIntegrable (fun t => star (f t) • B t)
      volume 0 (2 * Real.pi) := by
    rw [hstarf]
    exact hfB
  have hfK : IntervalIntegrable (fun t => f t • K t)
      volume 0 (2 * Real.pi) := by
    change IntervalIntegrable
      (fun t => f t • (B t + ContinuousLinearMap.adjoint (B t)))
      volume 0 (2 * Real.pi)
    exact intervalIntegrable_smul_add_adjoint B f hfB hstarfB
  have hKpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi), 0 ≤ K t := by
    intro t ht
    change 0 ≤ ((-I * deriv gamma t) • resolvent A (gamma t) +
      ContinuousLinearMap.adjoint
        ((-I * deriv gamma t) • resolvent A (gamma t)))
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    apply isPositive_add_adjoint_smul_resolvent A
    simpa only [gamma] using hsupport t ht
  have hfKpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      0 ≤ f t • K t := by
    intro t ht
    rw [show f t = ((‖Polynomial.eval (gamma t) p‖ ^ 2 : ℝ) : ℂ) by
      simp only [f]
      change (starRingEnd ℂ) (Polynomial.eval (gamma t) p) *
        Polynomial.eval (gamma t) p = _
      rw [Complex.conj_mul']
      norm_cast]
    change 0 ≤ (‖Polynomial.eval (gamma t) p‖ ^ 2 : ℝ) • K t
    exact smul_nonneg (sq_nonneg _) (hKpos t ht)
  have hIntegralPos : ContinuousLinearMap.IsPositive
      (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t) := by
    apply ContinuousLinearMap.isPositive_intervalIntegral
      (f := fun t => f t • K t) Real.two_pi_pos.le hfK
    exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => by
      rw [← ContinuousLinearMap.nonneg_iff_isPositive]
      exact hfKpos t ht
  have hsymmIntegral :
      (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) +
          ContinuousLinearMap.adjoint
            (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) =
        ∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t := by
    have h := ContinuousLinearMap.intervalIntegral_smul_add_adjoint
      B f hfB hstarfB
    rw [hstarf] at h
    simpa only [K] using h
  have hcoeff : ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-I)) =
      (2 * (Real.pi : ℂ) * I)⁻¹ := by
    symm
    calc
      (2 * (Real.pi : ℂ) * I)⁻¹ = I⁻¹ * (2 * (Real.pi : ℂ))⁻¹ :=
        mul_inv_rev _ _
      _ = (-I) * (2 * (Real.pi : ℂ))⁻¹ := by rw [inv_I]
      _ = (-I) * ((((2 * Real.pi)⁻¹ : ℝ) : ℂ)) := by
        rw [Complex.ofReal_inv]
        push_cast
        rfl
      _ = ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-I)) := mul_comm _ _
  have haux : crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) =
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
        (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) := by
    unfold crouzeixAuxiliaryOperator contourIntegral
    have hfun :
        (fun t => f t • B t) = fun t =>
          (-I) • (deriv gamma t •
            ((star (Polynomial.eval (gamma t) p) *
              Polynomial.eval (gamma t) p) • resolvent A (gamma t))) := by
      funext t
      simp only [f, B, smul_smul]
      congr 1
      ring
    rw [hfun, intervalIntegral.integral_smul, smul_smul, hcoeff]
  have hsymm :
      crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) +
        star (crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)) =
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
        (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t) := by
    rw [haux]
    change
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
          (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t)) +
        ContinuousLinearMap.adjoint
          ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
            (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t)) = _
    rw [map_smulₛₗ, Complex.conj_ofReal, ← smul_add, hsymmIntegral]
  have hIntegralRe : 0 ≤ RCLike.re ⟪x,
      (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t) x⟫_ℂ :=
    hIntegralPos.re_inner_nonneg_right x
  have hsymmRe : 0 ≤ RCLike.re ⟪x,
      (crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) +
        star (crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p))) x⟫_ℂ := by
    rw [hsymm, smul_apply, inner_smul_right]
    change 0 ≤
      (((((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
        ⟪x, (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t) x⟫_ℂ).re)
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr Real.two_pi_pos.le) hIntegralRe
  have hadjointRe : RCLike.re ⟪x,
      star (crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)) x⟫_ℂ =
      RCLike.re ⟪x,
        crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) x⟫_ℂ := by
    change RCLike.re ⟪x,
      ContinuousLinearMap.adjoint (crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)) x⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact inner_re_symm _ _
  rw [add_apply, inner_add_right, map_add, hadjointRe] at hsymmRe
  linarith
