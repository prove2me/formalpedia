-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_signed_jump_kernel_pos_neg_count_tsum
-- name    : AvramDividend.Classical.avram_p3_2_original_signed_jump_kernel_pos_neg_count_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:52:06.9406+00:00
-- url     : https://prove2.me/theorems/5a6da9d6-1db3-4d0e-aa28-b3effc95e10b
-- title:
--   Actual original Lévy signed nonlinear jump kernel has exact positive and negative count-tsum representations
-- statement:
--   For every original Lévy path, the positive and negative ENNReal parts of any measurable real signed nonlinear jump kernel have exact source-jump-counting integrals equal to the corresponding time-indexed jump tsums. This prepares the signed L1 original E2 compensator expression without assuming the raw kernel nonnegative or suppressing jumps at zero.
-- source:
--   Source-specific original nonlinear count-tsum theorem and pinned ENNReal measurable-ofReal, with explicitly measurable signed kernel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Both positive and negative nonnegative-part integrals of the actual
signed original Lévy nonlinear jump kernel equal their actual jump tsums. -/

theorem AvramDividend.Classical.avram_p3_2_original_signed_jump_kernel_pos_neg_count_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ) (hF : Measurable F) :
    let NX : Measure (ℝ≥0 × ℝ) := ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ((∫⁻ p, ENNReal.ofReal (F p) ∂NX) =
       ∑' u : ℝ≥0, if 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then ENNReal.ofReal (F (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) else 0) ∧
    ((∫⁻ p, ENNReal.ofReal (-F p) ∂NX) =
       ∑' u : ℝ≥0, if 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then ENNReal.ofReal (-F (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) else 0) := by sorry
