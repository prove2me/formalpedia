-- Prove2me | solution 1 for smul_add_smul_mem_numericalRange_of_mem_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:34.838051+00:00
-- url     : https://prove2.me/submissions/e8f1b3c5-dfaf-4a7f-be80-273f475eec35

import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers
import Theorems.Thm_inner_smul_sub_smul_one_apply_self

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E)
    {z₀ z₁ : ℂ} (hz : z₀ ≠ z₁)
    {a b : ℝ} (hab : a + b = 1)
    (hb : (b : ℂ) ∈ numericalRange ((z₁ - z₀)⁻¹ • (A - z₀ • 1))) :
    a • z₀ + b • z₁ ∈ numericalRange A := by
  obtain ⟨x, hx, hinner⟩ := hb
  refine ⟨x, hx, ?_⟩
  rw [inner_smul_sub_smul_one_apply_self _ _ A hx] at hinner
  have hdenom : z₁ - z₀ ≠ 0 := sub_ne_zero.mpr hz.symm
  field_simp [hdenom] at hinner
  have habc := congrArg (fun r : ℝ => (r : ℂ)) hab
  push_cast at habc
  change ⟪x, A x⟫_ℂ = (a : ℂ) * z₀ + (b : ℂ) * z₁
  calc
    ⟪x, A x⟫_ℂ = z₀ + (⟪x, A x⟫_ℂ - z₀) := by ring
    _ = z₀ + (z₁ - z₀) * (b : ℂ) := by rw [hinner]
    _ = ((a : ℂ) + (b : ℂ)) * z₀ + (z₁ - z₀) * (b : ℂ) := by
      rw [habc, one_mul]
    _ = (a : ℂ) * z₀ + (b : ℂ) * z₁ := by ring
