-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_finite_jump_test_count_integral_v2
-- name    : AvramDividend.Classical.avram_p2_a_assist_original_finite_jump_test_count_integral_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:48:56.117332+00:00
-- url     : https://prove2.me/theorems/5d539a2e-3622-4584-9efd-97f2c550af80
-- title:
--   Original finite-horizon intrinsic marked counting integral equals finite actual jump sum (full pinned source environment)
-- statement:
--   For the genuine original spectrally negative Lévy process, a nonnegative measurable mark test and exact finite support F of marked jumps on (0,T] give a source-exact identity between the counting-map integral restricted to that time horizon and ENNReal.ofReal of the actual finite marked jump sum. Uses measurable original jump mark path, measurable actual jump-time set, and the Proved generic finite counting integral identity; no compensator or rate premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_finite_weighted_mark_count_real_sum

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_a_assist_original_finite_jump_test_count_integral_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0)
    (f : ℝ → ℝ) (hf : Measurable f) (hfpos : ∀ y, 0 ≤ f y)
    (F : Finset ℝ≥0)
    (hF : ∀ u : ℝ≥0, u ∈ F ↔
      (0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      u ∈ Ioc 0 T ∧
      f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) :
    (∫⁻ p in (Ioc 0 T ×ˢ (Set.univ : Set ℝ)),
      ENNReal.ofReal (f p.2) ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ENNReal.ofReal (∑ u ∈ F,
        f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
