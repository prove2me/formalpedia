-- Prove2me | solution 1 for image_neg_star_centeredNumericalRadiusMinimizers_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:43:02.653917+00:00
-- url     : https://prove2.me/submissions/cef36227-2d1d-4e42-8f1d-2953dfd8ab5a

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_numericalRadius_one
import Theorems.Thm_numericalRadius_smul_one
import Theorems.Thm_centeredNumericalRadiusMinimizers_neg
import Theorems.Thm_centeredNumericalRadiusMinimizers_zero
import Theorems.Thm_centeredNumericalRadiusMinimizers_smul_one
import Theorems.Thm_star_mem_centeredNumericalRadiusMinimizers_iff
import Theorems.Thm_neg_star_mem_centeredNumericalRadiusMinimizers_iff
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_adjoint
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_numericalRange_scalar
import Theorems.Thm_numericalRange_zero
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_adjoint
attribute [local simp] numericalRadius_neg
attribute [local simp] numericalRange_scalar
attribute [local simp] numericalRange_zero


attribute [local simp] numericalRadius_one
attribute [local simp] numericalRadius_smul_one
attribute [local simp] centeredNumericalRadiusMinimizers_neg
attribute [local simp] centeredNumericalRadiusMinimizers_zero
attribute [local simp] centeredNumericalRadiusMinimizers_smul_one
attribute [local simp] star_mem_centeredNumericalRadiusMinimizers_iff
attribute [local simp] neg_star_mem_centeredNumericalRadiusMinimizers_iff

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
omit [Nontrivial E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) :
    (fun c : ℂ => -star c) '' centeredNumericalRadiusMinimizers A =
      centeredNumericalRadiusMinimizers A := by
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact (neg_star_mem_centeredNumericalRadiusMinimizers_iff A hA d).2 hd
  · intro hc
    refine ⟨-star c,
      (neg_star_mem_centeredNumericalRadiusMinimizers_iff A hA c).2 hc, ?_⟩
    simp only [star_neg, star_star, neg_neg]
