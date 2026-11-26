-- Prove2me | solution 1 for exists_nonneg_bound_crouzeixPolynomialScalarCompanionNumerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:53.872002+00:00
-- url     : https://prove2.me/submissions/be3fcd49-bfaf-4f7c-b454-78c19769dd72

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay

set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤ C := by
  have hintegrand : ContinuousOn
      (fun t ↦ deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p))
      (Icc (0 : ℝ) (2 * Real.pi)) :=
    (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn.mul
      ((p.continuous.comp
        Omega.boundaryParam_contDiff.continuous).star.continuousOn)
  have himage : IsCompact
      ((fun t ↦ deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p)) ''
          Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.image_of_continuousOn hintegrand
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
    himage.isBounded
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * Real.pi) :=
    ⟨le_rfl, Real.two_pi_pos.le⟩
  have hC_nonneg : 0 ≤ C := by
    have hmem := hC ⟨0, hzero, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact (norm_nonneg _).trans hmem
  refine ⟨C, hC_nonneg, fun t ht ↦ ?_⟩
  have hmem := hC ⟨t, ht, rfl⟩
  rwa [Metric.mem_closedBall, dist_zero_right] at hmem
