-- Prove2me | solution 1 for numericalRange_nonempty_iff_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:23.566264+00:00
-- url     : https://prove2.me/submissions/954f1e2d-19b5-4147-8951-a41804677b1b

import Mathlib.Analysis.Normed.Module.Normalize
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Nonempty
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    (numericalRange A).Nonempty ↔ Nontrivial E := by
  constructor
  · rintro ⟨z, x, hx, _hz⟩
    rw [nontrivial_iff_exists_ne (0 : E)]
    refine ⟨x, ?_⟩
    intro hzero
    subst x
    norm_num at hx
  · intro hE
    obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (0 : E)).mp hE
    let u : E := NormedSpace.normalize x
    have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hx
    exact ⟨⟪u, A u⟫_ℂ, (mem_numericalRange A _).2 ⟨u, hu, rfl⟩⟩
