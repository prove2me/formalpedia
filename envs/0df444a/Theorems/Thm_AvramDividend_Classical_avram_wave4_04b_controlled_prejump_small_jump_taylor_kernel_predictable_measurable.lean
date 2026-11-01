-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_small_jump_taylor_kernel_predictable_measurable
-- name    : AvramDividend.Classical.avram_wave4_04b_controlled_prejump_small_jump_taylor_kernel_predictable_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:35:44.066785+00:00
-- url     : https://prove2.me/theorems/01915016-e368-4ded-bd3c-712a888e9694
-- title:
--   Actual controlled source-X pre-jump Taylor remainder is predictable jointly in its Lévy mark
-- statement:
--   For the original spectrally negative Lévy path with actual adapted dividend strategy and corrected value boundary/strict-cap C² hypotheses, the full small-jump Taylor remainder w(U^-+z)−w(U^-)−z · [1_{interior}w'(U^-)] is jointly measurable on the right-continuous predictable time–sample σ-algebra and the Borel mark z. Includes arbitrarily negative ruin-crossing marks and does not conflate source left jumps with subsequent dividend right-payment atoms. It does not claim PRM compensation, finite quadratic moment or Ito–Meyer.
-- source:
--   Compose the proven source-X strongly predictable left-limit reserve, globally Borel corrected value function, generic marked increment kernel, and exact-cap interior derivative Borel zero-extension in the product predictable σ-algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_corrected_value_global_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_marked_value_increment_measurable_of_process_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_controlled_prejump_small_jump_taylor_kernel_predictable_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    Measurable[(𝓕.rightCont.predictable).prod inferInstance]
      (fun z : (ℝ≥0 × Ω) × ℝ =>
        let a := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s z.1.2 - rightLimit D s z.1.2)
          z.1.1
        let d := if 0 < a ∧ ENNReal.ofReal a < C then deriv w a else 0
        w (a + z.2) - w a - d * z.2) := by
  sorry
