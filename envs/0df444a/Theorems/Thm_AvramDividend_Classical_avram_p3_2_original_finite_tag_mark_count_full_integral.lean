-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_tag_mark_count_full_integral
-- name    : AvramDividend.Classical.avram_p3_2_original_finite_tag_mark_count_full_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:19:18.814559+00:00
-- url     : https://prove2.me/theorems/e08fc4eb-3e7a-42ba-903c-ee1fb0f81fdc
-- title:
--   Finite genuine original Lévy jump tags exactly counted in nonlinear marked integral
-- statement:
--   Any finite tagged set of positive-time nonzero original Lévy jumps is counted exactly once by the original marked counting integral, and the integral of a nonnegative measurable nonlinear kernel restricted to those jump times is the finite sum of kernel evaluations at the actual jumps.
-- source:
--   Original spectrally negative Lévy X, Proved original joint jump-mark measurability 9d68c5c2 and original time support measurability 0a4c69be, Mathlib count/map/indicator lintegral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Finite tagged original Lévy jumps are counted exactly once by the
nonlinear original marked counting integral. -/

theorem AvramDividend.Classical.avram_p3_2_original_finite_tag_mark_count_full_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : Finset ℝ≥0)
    (hT : ∀ t ∈ T, 0 < t ∧
      X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p,
      (if p.1 ∈ (T : Set ℝ≥0) then F p else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑ t ∈ T, F (t,
        X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t) := by sorry
