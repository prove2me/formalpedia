-- Prove2me | solution 1 for star_mem_centeredNumericalRadiusMinimizers_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:16:16.32455+00:00
-- url     : https://prove2.me/submissions/eae2eacd-e639-4f73-84d9-83ed3be92a43

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
import Theorems.Thm_image_starRingEnd_centeredNumericalRadiusMinimizers_eq
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

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
omit [Nontrivial E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (c : ℂ) :
    star c ∈ centeredNumericalRadiusMinimizers A ↔
      c ∈ centeredNumericalRadiusMinimizers A := by
  have hmap {z : ℂ} (hz : z ∈ centeredNumericalRadiusMinimizers A) :
      star z ∈ centeredNumericalRadiusMinimizers A := by
    have himage :
        star z ∈ (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A :=
      ⟨z, hz, rfl⟩
    rwa [image_starRingEnd_centeredNumericalRadiusMinimizers_eq A hA] at himage
  constructor
  · intro hc
    simpa only [star_star] using hmap hc
  · exact hmap
