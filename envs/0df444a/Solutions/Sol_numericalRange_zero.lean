-- Prove2me | solution 1 for numericalRange_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:17.281494+00:00
-- url     : https://prove2.me/submissions/402f79e8-adf7-42d9-a622-49732e1ba9e8

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_NumericalRange_Affine
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [Nontrivial E] :
    numericalRange (0 : E →L[ℂ] E) = {0} := by
  ext z
  constructor
  · rintro ⟨x, _hx, hz⟩
    rw [mem_singleton_iff]
    simpa only [zero_apply, inner_zero_right] using hz.symm
  · intro hz
    rw [mem_singleton_iff] at hz
    subst z
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    exact (mem_numericalRange _ _).2 ⟨x, hxnorm, by simp⟩
