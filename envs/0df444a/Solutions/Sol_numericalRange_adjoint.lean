-- Prove2me | solution 1 for numericalRange_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:25:13.955305+00:00
-- url     : https://prove2.me/submissions/e2db55b5-2577-4eaf-9379-7c7d8c038c4e

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Adjoint

set_option autoImplicit false
open scoped InnerProductSpace
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) :
    numericalRange (ContinuousLinearMap.adjoint A) =
      (starRingEnd ℂ) '' (numericalRange A) := by
  ext z
  constructor
  · rintro ⟨x, hx, hz⟩
    refine ⟨⟪x, A x⟫_ℂ, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hz, adjoint_inner_right, inner_conj_symm]
  · rintro ⟨w, ⟨x, hx, hxw⟩, hwz⟩
    refine ⟨x, hx, ?_⟩
    rw [adjoint_inner_right, ← inner_conj_symm, hxw, hwz]
