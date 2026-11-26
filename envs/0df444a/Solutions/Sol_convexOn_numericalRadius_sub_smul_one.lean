-- Prove2me | solution 1 for convexOn_numericalRadius_sub_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:36.939259+00:00
-- url     : https://prove2.me/submissions/97d65cc8-c45b-4730-b688-717a7c2f84e8

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_numericalRadius_one
import Theorems.Thm_numericalRadius_smul_one
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

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
omit [Nontrivial E]
theorem _root_.solution (A : E →L[ℂ] E) :
    ConvexOn ℝ Set.univ (fun c : ℂ => numericalRadius (A - c • 1)) := by
  refine ⟨convex_univ, fun c _ d _ a b ha hb hab => ?_⟩
  have habC : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
  have hop :
      A - (a • c + b • d) • 1 =
        (a : ℂ) • (A - c • 1) + (b : ℂ) • (A - d • 1) := by
    calc
      A - (a • c + b • d) • 1 =
          ((a : ℂ) + (b : ℂ)) • A - (a • c + b • d) • 1 := by
        rw [habC, one_smul]
      _ = (a : ℂ) • (A - c • 1) + (b : ℂ) • (A - d • 1) := by
        simp only [Complex.real_smul]
        module
  change numericalRadius (A - (a • c + b • d) • 1) ≤
    a * numericalRadius (A - c • 1) +
      b * numericalRadius (A - d • 1)
  rw [hop]
  calc
    numericalRadius
        ((a : ℂ) • (A - c • 1) + (b : ℂ) • (A - d • 1)) ≤
        numericalRadius ((a : ℂ) • (A - c • 1)) +
          numericalRadius ((b : ℂ) • (A - d • 1)) :=
      numericalRadius_add_le _ _
    _ = a * numericalRadius (A - c • 1) +
        b * numericalRadius (A - d • 1) := by
      rw [numericalRadius_smul, numericalRadius_smul, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
