-- Prove2me | solution 1 for numericalRange_compression_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:14:19.94749+00:00
-- url     : https://prove2.me/submissions/2adea0d7-d4f1-45a3-88bb-d41429ded5b3

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_Compression
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_neg
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_neg



set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
theorem _root_.solution
    (A : E →L[ℂ] E) (V : F →L[ℂ] E) (hV : Isometry V) :
    numericalRange ((V† ∘L A) ∘L V) ⊆ numericalRange A := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ :=
    (mem_numericalRange ((V† ∘L A) ∘L V) z).mp hz
  have hVnorm : ‖V x‖ = ‖x‖ := by
    calc
      ‖V x‖ = dist (V x) (V 0) := by rw [map_zero, dist_zero_right]
      _ = dist x 0 := hV.dist_eq x 0
      _ = ‖x‖ := by rw [dist_zero_right]
  refine (mem_numericalRange A _).2 ⟨V x, hVnorm.trans hx, ?_⟩
  simp only [ContinuousLinearMap.comp_apply]
  rw [adjoint_inner_right]
