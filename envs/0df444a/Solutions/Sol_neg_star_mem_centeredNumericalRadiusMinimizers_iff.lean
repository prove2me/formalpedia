-- Prove2me | solution 1 for neg_star_mem_centeredNumericalRadiusMinimizers_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:10.901569+00:00
-- url     : https://prove2.me/submissions/03851abc-97c3-4302-bcff-f87c26a30cc7

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
import Theorems.Thm_centeredNumericalRadiusMinimizers_adjoint
import Theorems.Thm_star_mem_centeredNumericalRadiusMinimizers_iff
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

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
omit [Nontrivial E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) (c : ℂ) :
    -star c ∈ centeredNumericalRadiusMinimizers A ↔
      c ∈ centeredNumericalRadiusMinimizers A := by
  have hAadj : A† = -A := skewAdjoint.mem_iff.mp hA
  have himages :
      (fun z : ℂ => -z) '' centeredNumericalRadiusMinimizers A =
        (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A := by
    calc
      _ = centeredNumericalRadiusMinimizers (-A) :=
        (centeredNumericalRadiusMinimizers_neg A).symm
      _ = centeredNumericalRadiusMinimizers (A†) := by rw [hAadj]
      _ = _ := centeredNumericalRadiusMinimizers_adjoint A
  have hmap {z : ℂ} (hz : z ∈ centeredNumericalRadiusMinimizers A) :
      -star z ∈ centeredNumericalRadiusMinimizers A := by
    have hzstar :
        star z ∈ (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A :=
      ⟨z, hz, rfl⟩
    rw [← himages] at hzstar
    obtain ⟨d, hd, hdz⟩ := hzstar
    have hd_eq : d = -star z := by
      rw [← hdz]
      simp only [neg_neg]
    rwa [← hd_eq]
  constructor
  · intro hc
    simpa only [star_neg, star_star, neg_neg] using hmap hc
  · exact hmap
