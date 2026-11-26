-- Prove2me | solution 1 for inner_apply_real_smul_add_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:30.222603+00:00
-- url     : https://prove2.me/submissions/305dea66-fc0c-4119-82f9-7bdf4529e95e

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E)
    (x₀ x₁ : E) (ω : ℂ) (u v : ℝ) :
    ⟪(u : ℂ) • x₀ + (v : ℂ) • (ω • x₁),
      A ((u : ℂ) • x₀ + (v : ℂ) • (ω • x₁))⟫_ℂ =
    (u : ℂ) ^ 2 * ⟪x₀, A x₀⟫_ℂ +
      ((u * v : ℝ) : ℂ) *
        (ω * ⟪x₀, A x₁⟫_ℂ + starRingEnd ℂ ω * ⟪x₁, A x₀⟫_ℂ) +
      (v : ℂ) ^ 2 * (‖ω‖ ^ 2 : ℂ) * ⟪x₁, A x₁⟫_ℂ := by
  simp only [map_add, map_smul]
  simp only [inner_add_left, inner_add_right]
  simp only [inner_smul_left, inner_smul_right]
  rw [← Complex.conj_mul' ω]
  simp only [Complex.conj_ofReal]
  push_cast
  ring
