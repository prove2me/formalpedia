-- Prove2me | solution 1 for norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_of_cauchy_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:35.495176+00:00
-- url     : https://prove2.me/submissions/65b24537-99d5-4759-ab01-e83cf9c85749

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Theorems.Thm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
import Theorems.Thm_crouzeixAuxiliaryIntegrand_contourIntegrable
import Theorems.Thm_intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy
import Theorems.Thm_isPositive_add_adjoint_smul_resolvent
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_add_star_le_two_mul_of_doubleLayer_representation
attribute [local simp] mem_numericalRange


section
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace SmoothJordanDomain
end SmoothJordanDomain
private theorem intervalIntegrable_deriv_smul_resolvent
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    IntervalIntegrable
      (fun t => deriv Omega.boundaryParam t •
        resolvent A (Omega.boundaryParam t))
      volume 0 (2 * Real.pi) := by
  have hcontour :=
    crouzeixAuxiliaryIntegrand_contourIntegrable A Omega
      (fun _ => 1) hOmega continuous_const.continuousOn
  change IntervalIntegrable
    (fun t => deriv Omega.boundaryParam t •
      (1 • resolvent A (Omega.boundaryParam t)))
    volume 0 (2 * Real.pi) at hcontour
  simpa only [one_smul] using hcontour
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
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {M : ℝ}
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
          (w - Omega.boundaryParam t)).re ≤ 0)
    (hM : 0 ≤ M)
    (hp : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ‖Polynomial.eval (Omega.boundaryParam t) p‖ ≤ M) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤ 2 * M := by
  let gamma := Omega.boundaryParam
  let f : ℝ → ℂ := fun t => Polynomial.eval (gamma t) p
  let B : ℝ → E →L[ℂ] E := fun t =>
    (-I * deriv gamma t) • resolvent A (gamma t)
  let K : ℝ → E →L[ℂ] E := fun t =>
    B t + ContinuousLinearMap.adjoint (B t)
  have hbase : IntervalIntegrable
      (fun t => deriv gamma t • resolvent A (gamma t))
      volume 0 (2 * Real.pi) := by
    simpa only [gamma] using
      intervalIntegrable_deriv_smul_resolvent A Omega hOmega
  have hB : IntervalIntegrable B volume 0 (2 * Real.pi) := by
    simpa only [B, gamma, one_smul] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel
        A Omega (fun _ => 1) hOmega continuous_const.continuousOn
  have hK : IntervalIntegrable K volume 0 (2 * Real.pi) := by
    change IntervalIntegrable
      (fun t => B t + ContinuousLinearMap.adjoint (B t))
      volume 0 (2 * Real.pi)
    exact hB.add (intervalIntegrable_adjoint hB)
  have hfB : IntervalIntegrable (fun t => f t • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel
        A Omega (fun z => Polynomial.eval z p) hOmega
          p.continuous.continuousOn
  have hstarfB : IntervalIntegrable (fun t => star (f t) • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel
        A Omega (fun z => star (Polynomial.eval z p)) hOmega
          p.continuous.star.continuousOn
  have hfK : IntervalIntegrable (fun t => f t • K t)
      volume 0 (2 * Real.pi) := by
    change IntervalIntegrable
      (fun t => f t • (B t + ContinuousLinearMap.adjoint (B t)))
      volume 0 (2 * Real.pi)
    exact intervalIntegrable_smul_add_adjoint B f hfB hstarfB
  have hrepresentation :
      Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A Omega p) =
        (2 * Real.pi)⁻¹ •
          (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t) := by
    simpa only [gamma, f, B, K] using
      (aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
        A Omega p hOmega hCauchyP)
  have hpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi), 0 ≤ K t := by
    intro t ht
    change 0 ≤ ((-I * deriv gamma t) • resolvent A (gamma t) +
      ContinuousLinearMap.adjoint
        ((-I * deriv gamma t) • resolvent A (gamma t)))
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    apply isPositive_add_adjoint_smul_resolvent A
    simpa only [gamma] using hsupport t ht
  have hCauchyOne' :
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        deriv gamma t • resolvent A (gamma t)) =
          (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
    simpa only [gamma] using hCauchyOne
  have hnorm : (∫ t in (0 : ℝ)..(2 * Real.pi), K t) =
      (4 * Real.pi) • (1 : E →L[ℂ] E) := by
    simpa only [K, B] using
      (intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy
        A gamma hbase hCauchyOne')
  have hp' : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi), ‖f t‖ ≤ M := by
    simpa only [f, gamma] using hp
  exact norm_add_star_le_two_mul_of_doubleLayer_representation
    (Polynomial.aeval A p) (crouzeixPolynomialAuxiliaryOperator A Omega p)
      hrepresentation hK hfK hpos hnorm hM hp'
