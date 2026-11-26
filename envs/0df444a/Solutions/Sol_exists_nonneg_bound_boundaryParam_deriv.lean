-- Prove2me | solution 1 for exists_nonneg_bound_boundaryParam_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:55:11.507799+00:00
-- url     : https://prove2.me/submissions/a9226fd4-80c9-476b-b1a2-8b27f48c2479

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay

set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D := by
  have hderiv : ContinuousOn (deriv Omega.boundaryParam)
      (Icc (0 : ℝ) (2 * Real.pi)) :=
    (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  have himage : IsCompact
      (deriv Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.image_of_continuousOn hderiv
  obtain ⟨D, hD⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
    himage.isBounded
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * Real.pi) :=
    ⟨le_rfl, Real.two_pi_pos.le⟩
  have hD_nonneg : 0 ≤ D := by
    have hmem := hD ⟨0, hzero, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact (norm_nonneg _).trans hmem
  refine ⟨D, hD_nonneg, fun t ht ↦ ?_⟩
  have hmem := hD ⟨t, ht, rfl⟩
  rwa [Metric.mem_closedBall, dist_zero_right] at hmem
