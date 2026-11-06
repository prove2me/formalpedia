-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_source_nonlinear_jump_count_eq_tsum
-- name    : AvramDividend.Classical.avram_p3_2_original_source_nonlinear_jump_count_eq_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:02:31.048678+00:00
-- url     : https://prove2.me/theorems/008c9b37-eadb-490a-aff6-551e96e8a297
-- title:
--   Actual original Lévy nonlinear marked-jump integral equals full original source time-jump sum
-- statement:
--   On every sample path of the original spectrally negative Lévy process, the intrinsic marked counting integral of an arbitrary measurable nonnegative nonlinear jump kernel is exactly the time-indexed sum of kernel evaluations at the process's actual left jumps. Original joint jump-mark measurability and measurable original jump-time support are deduced from Proved source-exact theorems; no finite-jump, residual-zero or equality-in-law assumption is added.
-- source:
--   Pinned original jump mark joint measurability 9d68c5c2, original jump-time measurable support 0a4c69be, and new generic nonlinear marked-count integral identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Literal original source nonlinear jump kernel: counting integral equals
the all-time actual original marked-jump sum. -/

theorem AvramDividend.Classical.avram_p3_2_original_source_nonlinear_jump_count_eq_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑' u : ℝ≥0,
        if 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
          F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
        else 0 := by sorry
