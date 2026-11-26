-- Prove2me | solution 1 for norm_inv_two_pi_smul_intervalIntegral_le_two_mul_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:05.027911+00:00
-- url     : https://prove2.me/submissions/5c1dff32-d706-44cf-985c-d4112c3af7b8

import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveKernelBound
import Definitions.Def_Operator_Crouzeix_DoubleLayerBound
import Theorems.Thm_norm_intervalIntegral_smul_le_of_nonneg


set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    {K : ℝ → E →L[ℂ] E} {f : ℝ → ℂ} {M : ℝ}
    (hK : IntervalIntegrable K volume 0 (2 * Real.pi))
    (hfK : IntervalIntegrable (fun t ↦ f t • K t) volume 0 (2 * Real.pi))
    (hpos : ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), 0 ≤ K t)
    (hnorm : ∫ t in (0 : ℝ)..(2 * Real.pi), K t =
      (4 * Real.pi) • (1 : E →L[ℂ] E))
    (hM : 0 ≤ M) (hf : ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), ‖f t‖ ≤ M) :
    ‖(2 * Real.pi)⁻¹ • (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t)‖ ≤ 2 * M := by
  have hcontract : ‖∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t‖ ≤
      (4 * Real.pi) * M :=
    norm_intervalIntegral_smul_le_of_nonneg Real.two_pi_pos.le hK hfK hpos hnorm
      (by positivity) hM hf
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr Real.two_pi_pos)]
  calc
    (2 * Real.pi)⁻¹ * ‖∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t‖ ≤
        (2 * Real.pi)⁻¹ * ((4 * Real.pi) * M) :=
      mul_le_mul_of_nonneg_left hcontract (inv_nonneg.mpr Real.two_pi_pos.le)
    _ = 2 * M := by
      field_simp [Real.pi_ne_zero]
      ring
