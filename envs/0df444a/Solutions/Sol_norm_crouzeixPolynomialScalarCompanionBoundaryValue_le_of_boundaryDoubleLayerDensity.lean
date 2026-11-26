-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanionBoundaryValue_le_of_boundaryDoubleLayerDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:32.152512+00:00
-- url     : https://prove2.me/submissions/fcbaf06d-8707-4585-af85-4b62b3d4a2a6

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_eq_integral_boundaryDoubleLayerDensity
import Theorems.Thm_ContinuousLinearMap_integral_mono_ae
import Theorems.Thm_norm_eval_boundaryParam_le_polynomialSupNorm_frontier


set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier)
    (hrho : IntervalIntegrable
      (crouzeixBoundaryDoubleLayerDensity Omega xi)
      volume 0 (2 * Real.pi))
    (hmass : (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t) :
    ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  let rho := crouzeixBoundaryDoubleLayerDensity Omega xi
  let M := polynomialSupNorm p (frontier Omega.carrier)
  have hrhoC : IntervalIntegrable (fun t => (rho t : ℂ))
      volume 0 (2 * Real.pi) := by
    constructor
    · change IntegrableOn (fun t => Complex.ofRealCLM (rho t))
        (Ioc 0 (2 * Real.pi)) volume
      exact Complex.ofRealCLM.integrable_comp hrho.1
    · change IntegrableOn (fun t => Complex.ofRealCLM (rho t))
        (Ioc (2 * Real.pi) 0) volume
      exact Complex.ofRealCLM.integrable_comp hrho.2
  have hpcont : Continuous (fun t : ℝ =>
      star (Polynomial.eval (Omega.boundaryParam t) p)) :=
    p.continuous.comp Omega.boundaryParam_contDiff.continuous |>.star
  have hweighted : IntervalIntegrable
      (fun t => (rho t : ℂ) *
        star (Polynomial.eval (Omega.boundaryParam t) p))
      volume 0 (2 * Real.pi) :=
    hrhoC.mul_continuousOn hpcont.continuousOn
  have hweightedOn : Integrable
      (fun t => (rho t : ℂ) *
        star (Polynomial.eval (Omega.boundaryParam t) p))
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      Real.two_pi_pos.le).mp hweighted
  have hrhoOn : Integrable rho
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      Real.two_pi_pos.le).mp hrho
  have hrhs : Integrable (fun t => rho t * M)
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    hrhoOn.mul_const M
  have hpoint : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))),
      ‖(rho t : ℂ) *
          star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤
        rho t * M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hrho_nonneg : 0 ≤ rho t := hpos t ht
    rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hrho_nonneg]
    exact mul_le_mul_of_nonneg_left
      (norm_eval_boundaryParam_le_polynomialSupNorm_frontier Omega p t)
      hrho_nonneg
  rw [
    crouzeixPolynomialScalarCompanionBoundaryValue_eq_integral_boundaryDoubleLayerDensity
      Omega p hxi hrho hmass,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    (∫ t in Ioc (0 : ℝ) (2 * Real.pi),
        ‖(rho t : ℂ) *
          star (Polynomial.eval (Omega.boundaryParam t) p)‖) ≤
        ∫ t in Ioc (0 : ℝ) (2 * Real.pi), rho t * M :=
      integral_mono_ae hweightedOn.norm hrhs hpoint
    _ = M := by
      rw [integral_mul_const,
        ← intervalIntegral.integral_of_le Real.two_pi_pos.le, hmass,
        one_mul]
