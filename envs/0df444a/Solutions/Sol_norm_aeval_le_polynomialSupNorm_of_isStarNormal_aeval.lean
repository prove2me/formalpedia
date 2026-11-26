-- Prove2me | solution 1 for norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:29.745017+00:00
-- url     : https://prove2.me/submissions/4dfe5a31-8ff3-4564-a9f4-e2ed93b611ce

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_Normal
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open Polynomial
theorem _root_.solution {A : Type*} [CStarAlgebra A]
    (a : A) {K : Set ℂ} (hK : IsCompact K) (hσ : spectrum ℂ a ⊆ K)
    (p : ℂ[X]) [IsStarNormal (aeval a p)] :
    ‖aeval a p‖ ≤ polynomialSupNorm p K := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (aeval a p) 0, norm_zero]
    exact polynomialSupNorm_nonneg p _
  have hM0 : 0 ≤ polynomialSupNorm p K := polynomialSupNorm_nonneg p _
  have hbound : spectralRadius ℂ (aeval a p) ≤ ((polynomialSupNorm p K).toNNReal : ENNReal) := by
    refine iSup₂_le fun k hk => ?_
    rw [spectrum.map_polynomial_aeval] at hk
    obtain ⟨z, hz, rfl⟩ := hk
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM0]
    exact norm_eval_le_polynomialSupNorm p (bddAbove_norm_eval_image_of_isCompact p hK) (hσ hz)
  rw [IsStarNormal.spectralRadius_eq_nnnorm (aeval a p), ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM0] at hbound
  exact hbound
