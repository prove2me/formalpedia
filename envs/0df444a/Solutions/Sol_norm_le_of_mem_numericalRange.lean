-- Prove2me | solution 1 for norm_le_of_mem_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:31:01.923241+00:00
-- url     : https://prove2.me/submissions/c93e370d-f58d-4d6e-bb0a-54ce7220497e

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc ‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm x (A x)
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by gcongr; exact A.le_opNorm x
    _ = ‖A‖ := by rw [hx]; ring
