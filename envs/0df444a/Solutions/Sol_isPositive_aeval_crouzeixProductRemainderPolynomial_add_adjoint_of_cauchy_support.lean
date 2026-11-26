-- Prove2me | solution 1 for isPositive_aeval_crouzeixProductRemainderPolynomial_add_adjoint_of_cauchy_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:08.812268+00:00
-- url     : https://prove2.me/submissions/b9488c99-f76e-4aca-8776-08784be2a85b

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Theorems.Thm_ContinuousLinearMap_intervalIntegral_add_adjoint
import Theorems.Thm_ContinuousLinearMap_isPositive_intervalIntegral
import Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
import Theorems.Thm_commute_aeval_crouzeixPolynomialAuxiliaryOperator
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
    (hCauchyP : Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam)
    (hCauchyOne : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv Omega.boundaryParam t • resolvent A (Omega.boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0) :
    ContinuousLinearMap.IsPositive
      (Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) +
        star (Polynomial.aeval A
          (crouzeixProductRemainderPolynomial Omega p))) := by
  let gamma := Omega.boundaryParam
  let f : ℝ → ℂ := fun t => Polynomial.eval (gamma t) p
  let B : ℝ → E →L[ℂ] E := fun t =>
    (-I * deriv gamma t) • resolvent A (gamma t)
  let K : ℝ → E →L[ℂ] E := fun t =>
    B t + ContinuousLinearMap.adjoint (B t)
  let F : E →L[ℂ] E := Polynomial.aeval A p
  let D : ℝ → E →L[ℂ] E := fun t => f t • 1 - F
  let Q : ℝ → E →L[ℂ] E := fun t => star (D t) * B t * D t
  have hB : IntervalIntegrable B volume 0 (2 * Real.pi) := by
    simpa only [B, gamma, one_smul] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel
        A Omega (fun _ => 1) hOmega continuous_const.continuousOn
  have hD : Continuous D := by
    have hgamma : Continuous gamma := by
      simpa only [gamma] using Omega.boundaryParam_contDiff.continuous
    change Continuous (fun t => f t • (1 : E →L[ℂ] E) - F)
    have hf : Continuous f := p.continuous.comp hgamma
    fun_prop
  have hQ : IntervalIntegrable Q volume 0 (2 * Real.pi) := by
    have hBD : IntervalIntegrable (fun t => B t * D t)
        volume 0 (2 * Real.pi) := hB.mul_continuousOn hD.continuousOn
    have hstarD : Continuous (fun t => star (D t)) := by
      fun_prop
    simpa only [Q, mul_assoc] using
      hBD.continuousOn_mul hstarD.continuousOn
  have hKpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ContinuousLinearMap.IsPositive (K t) := by
    intro t ht
    change ContinuousLinearMap.IsPositive
      ((-I * deriv gamma t) • resolvent A (gamma t) +
        ContinuousLinearMap.adjoint
          ((-I * deriv gamma t) • resolvent A (gamma t)))
    apply isPositive_add_adjoint_smul_resolvent A
    simpa only [gamma] using hsupport t ht
  have hQadd : (fun t => Q t + star (Q t)) =
      fun t => star (D t) * K t * D t := by
    funext t
    simp only [Q, K, star_mul, star_star, mul_add, add_mul, mul_assoc]
    rw [show star (B t) = ContinuousLinearMap.adjoint (B t) by rfl]
  have hQpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ContinuousLinearMap.IsPositive (Q t + star (Q t)) := by
    intro t ht
    rw [congrFun hQadd t]
    exact (hKpos t ht).adjoint_conj (D t)
  have hQsymm : ContinuousLinearMap.IsPositive
      (∫ t in (0 : ℝ)..(2 * Real.pi), Q t + star (Q t)) := by
    apply ContinuousLinearMap.isPositive_intervalIntegral
      (f := fun t => Q t + star (Q t)) Real.two_pi_pos.le
      (hQ.add (intervalIntegrable_adjoint hQ))
    exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => hQpos t ht
  have hQexpand : Q = fun t =>
      (star (f t) * f t) • B t -
        (star (f t) • B t) * F -
        star F * (f t • B t) +
        star F * B t * F := by
    funext t
    simp only [Q, D, star_sub, star_smul, star_one, sub_mul, mul_sub,
      one_mul, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc,
      smul_sub, smul_smul]
    rw [mul_comm (f t) (star (f t))]
    module
  let c : ℂ := (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
  have hcoeff : c * (-I) = (2 * (Real.pi : ℂ) * I)⁻¹ := by
    dsimp only [c]
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
  have hnormalized (h : ℂ → ℂ) :
      crouzeixAuxiliaryOperator A Omega h =
        c • (∫ t in (0 : ℝ)..(2 * Real.pi),
          h (gamma t) • B t) := by
    unfold crouzeixAuxiliaryOperator contourIntegral
    have hfun :
        (fun t => h (gamma t) • B t) = fun t =>
          (-I) • (deriv gamma t •
            (h (gamma t) • resolvent A (gamma t))) := by
      funext t
      simp only [B, smul_smul]
      congr 1
      ring
    rw [hfun, intervalIntegral.integral_smul, smul_smul, hcoeff]
  have habsB : IntervalIntegrable
      (fun t => (star (f t) * f t) • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) hOmega
        (p.continuous.star.mul p.continuous).continuousOn
  have hstarfB : IntervalIntegrable (fun t => star (f t) • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel A Omega
        (fun z => star (Polynomial.eval z p)) hOmega
        p.continuous.star.continuousOn
  have hfB : IntervalIntegrable (fun t => f t • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel A Omega
        (fun z => Polynomial.eval z p) hOmega p.continuous.continuousOn
  have hAbs : c • (∫ t in (0 : ℝ)..(2 * Real.pi),
        (star (f t) * f t) • B t) =
      crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) := by
    simpa only [f, gamma] using
      (hnormalized
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)).symm
  have hStar : c • (∫ t in (0 : ℝ)..(2 * Real.pi),
        star (f t) • B t) =
      crouzeixPolynomialAuxiliaryOperator A Omega p := by
    simpa only [crouzeixPolynomialAuxiliaryOperator, f, gamma] using
      (hnormalized (fun z => star (Polynomial.eval z p))).symm
  have hP : c • (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) = F := by
    rw [← hnormalized (fun z => Polynomial.eval z p)]
    unfold crouzeixAuxiliaryOperator
    simpa only [F] using hCauchyP.symm
  have hOne : c • (∫ t in (0 : ℝ)..(2 * Real.pi), B t) =
      (1 : E →L[ℂ] E) := by
    have hBfun : B = fun t =>
        (-I) • (deriv gamma t • resolvent A (gamma t)) := by
      funext t
      simp only [B, smul_smul]
    rw [hBfun, intervalIntegral.integral_smul]
    have hCauchyOne' :
        (∫ t in (0 : ℝ)..(2 * Real.pi),
          deriv gamma t • resolvent A (gamma t)) =
            (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
      simpa only [gamma] using hCauchyOne
    rw [hCauchyOne']
    simp only [smul_smul]
    rw [← mul_assoc, hcoeff, inv_mul_cancel₀]
    · exact one_smul ℂ (1 : E →L[ℂ] E)
    · exact mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hstarBF : IntervalIntegrable
      (fun t => (star (f t) • B t) * F) volume 0 (2 * Real.pi) :=
    hstarfB.mul_continuousOn continuous_const.continuousOn
  have hFstarfB : IntervalIntegrable
      (fun t => star F * (f t • B t)) volume 0 (2 * Real.pi) :=
    hfB.continuousOn_mul continuous_const.continuousOn
  have hFBF : IntervalIntegrable
      (fun t => star F * B t * F) volume 0 (2 * Real.pi) := by
    exact (hB.continuousOn_mul continuous_const.continuousOn).mul_continuousOn
      continuous_const.continuousOn
  have hintegral_mul_const (u : ℝ → E →L[ℂ] E) (C : E →L[ℂ] E)
      (hu : IntervalIntegrable u volume 0 (2 * Real.pi)) :
      (∫ t in (0 : ℝ)..(2 * Real.pi), u t * C) =
        (∫ t in (0 : ℝ)..(2 * Real.pi), u t) * C := by
    let L := (ContinuousLinearMap.mul ℝ (E →L[ℂ] E)).flip C
    change (∫ t in (0 : ℝ)..(2 * Real.pi), L (u t)) =
      L (∫ t in (0 : ℝ)..(2 * Real.pi), u t)
    exact L.intervalIntegral_comp_comm hu
  have hintegral_const_mul (C : E →L[ℂ] E) (u : ℝ → E →L[ℂ] E)
      (hu : IntervalIntegrable u volume 0 (2 * Real.pi)) :
      (∫ t in (0 : ℝ)..(2 * Real.pi), C * u t) =
        C * (∫ t in (0 : ℝ)..(2 * Real.pi), u t) := by
    let L := ContinuousLinearMap.mul ℝ (E →L[ℂ] E) C
    change (∫ t in (0 : ℝ)..(2 * Real.pi), L (u t)) =
      L (∫ t in (0 : ℝ)..(2 * Real.pi), u t)
    exact L.intervalIntegral_comp_comm hu
  have hIntegralQ :
      (∫ t in (0 : ℝ)..(2 * Real.pi), Q t) =
        (∫ t in (0 : ℝ)..(2 * Real.pi),
            (star (f t) * f t) • B t) -
          (∫ t in (0 : ℝ)..(2 * Real.pi), star (f t) • B t) * F -
          star F * (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) +
          star F * (∫ t in (0 : ℝ)..(2 * Real.pi), B t) * F := by
    rw [hQexpand]
    rw [intervalIntegral.integral_add
      ((habsB.sub hstarBF).sub hFstarfB) hFBF]
    rw [intervalIntegral.integral_sub (habsB.sub hstarBF) hFstarfB]
    rw [intervalIntegral.integral_sub habsB hstarBF]
    rw [hintegral_mul_const (fun t => star (f t) • B t) F hstarfB]
    rw [hintegral_const_mul (star F) (fun t => f t • B t) hfB]
    rw [hintegral_mul_const (fun t => star F * B t) F
      (hB.continuousOn_mul continuous_const.continuousOn)]
    rw [hintegral_const_mul (star F) B hB]
  have hStarF : c •
        ((∫ t in (0 : ℝ)..(2 * Real.pi), star (f t) • B t) * F) =
      crouzeixPolynomialAuxiliaryOperator A Omega p * F := by
    rw [← smul_mul_assoc, hStar]
  have hFP : c •
        (star F * (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t)) =
      star F * F := by
    rw [← mul_smul_comm, hP]
  have hFOneF : c •
        ((star F * (∫ t in (0 : ℝ)..(2 * Real.pi), B t)) * F) =
      star F * F := by
    rw [← smul_mul_assoc, ← mul_smul_comm, hOne, mul_one]
  have hQnorm : c • (∫ t in (0 : ℝ)..(2 * Real.pi), Q t) =
      Polynomial.aeval A
        (crouzeixProductRemainderPolynomial Omega p) := by
    rw [hIntegralQ]
    simp only [smul_add, smul_sub]
    rw [hAbs, hStarF, hFP, hFOneF]
    have hcomm :=
      commute_aeval_crouzeixPolynomialAuxiliaryOperator A Omega p p hOmega
    rw [← hcomm.eq]
    have hidentity :=
      aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
        A Omega p hOmega
    change crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) -
        Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p -
        star (Polynomial.aeval A p) * Polynomial.aeval A p +
        star (Polynomial.aeval A p) * Polynomial.aeval A p = _
    rw [hidentity]
    module
  have hcstar : (starRingEnd ℂ) c = c := by
    simp only [c, Complex.conj_ofReal]
  have hadjointQ : c • star (∫ t in (0 : ℝ)..(2 * Real.pi), Q t) =
      star (Polynomial.aeval A
        (crouzeixProductRemainderPolynomial Omega p)) := by
    rw [← hQnorm]
    change c • ContinuousLinearMap.adjoint
        (∫ t in (0 : ℝ)..(2 * Real.pi), Q t) =
      ContinuousLinearMap.adjoint
        (c • (∫ t in (0 : ℝ)..(2 * Real.pi), Q t))
    rw [map_smulₛₗ, hcstar]
  have hrepresentation :
      Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) +
          star (Polynomial.aeval A
          (crouzeixProductRemainderPolynomial Omega p)) =
        c • (∫ t in (0 : ℝ)..(2 * Real.pi), Q t + star (Q t)) := by
    change _ = c • (∫ t in (0 : ℝ)..(2 * Real.pi),
      Q t + ContinuousLinearMap.adjoint (Q t))
    rw [ContinuousLinearMap.intervalIntegral_add_adjoint hQ]
    change _ = c • ((∫ t in (0 : ℝ)..(2 * Real.pi), Q t) +
      star (∫ t in (0 : ℝ)..(2 * Real.pi), Q t))
    rw [smul_add, hQnorm, hadjointQ]
  rw [hrepresentation]
  rw [← ContinuousLinearMap.nonneg_iff_isPositive]
  change 0 ≤ (2 * Real.pi)⁻¹ •
    (∫ t in (0 : ℝ)..(2 * Real.pi), Q t + star (Q t))
  apply smul_nonneg (inv_nonneg.mpr Real.two_pi_pos.le)
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact hQsymm
