-- Prove2me | solution 1 for norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:37:57.951798+00:00
-- url     : https://prove2.me/submissions/78436207-8b41-4ac4-a7e6-6003540ba699

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_norm_eval_le_polynomialSupNorm
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact

set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
theorem _root_.solution {A : Type*} [CStarAlgebra A]
    {U : A} (hU : U ∈ unitary A) (p : ℂ[X]) :
    ‖aeval U p‖ ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (aeval U p) 0, norm_zero]
    exact polynomialSupNorm_nonneg p _
  haveI : IsStarNormal U := isStarNormal_of_mem_unitary hU
  haveI : IsStarNormal (aeval U p) := by
    rw [← cfc_polynomial p U]
    exact cfc_predicate _ U
  have hM0 : 0 ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) :=
    polynomialSupNorm_nonneg p _
  have hbound : spectralRadius ℂ (aeval U p) ≤
      ((polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1)).toNNReal : ENNReal) := by
    refine iSup₂_le fun k hk => ?_
    rw [spectrum.map_polynomial_aeval] at hk
    obtain ⟨z, hz, rfl⟩ := hk
    have hz1 : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.sphere_subset_closedBall (spectrum.subset_circle_of_unitary hU hz)
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM0]
    exact norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall (0 : ℂ) 1)) hz1
  rw [IsStarNormal.spectralRadius_eq_nnnorm (aeval U p), ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM0] at hbound
  exact hbound
