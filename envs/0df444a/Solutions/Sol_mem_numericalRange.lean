-- Prove2me | solution 1 for mem_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:31:58.283996+00:00
-- url     : https://prove2.me/submissions/05fec9d6-87c3-4311-9fec-a480014676e6

import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_Operator_NumericalRange_Basic

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) (z : ℂ) :
    z ∈ numericalRange A ↔ ∃ x : E, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z :=
  Iff.rfl
