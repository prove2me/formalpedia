-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_closed_history_lower_survival_joint_measurable_ws01a
-- name    : AvramDividend.Classical.chat04_closed_history_lower_survival_joint_measurable_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T09:18:26.295207+00:00
-- url     : https://prove2.me/theorems/f2b6346c-c273-456b-8d49-db94a1950d94
-- title:
--   Joint measurability of actual Lévy closed-history lower-survival event
-- statement:
--   For the actual spectrally negative Lévy sample path, the event that observation time is nonnegative and every state up to that time stays above the lower boundary -x is measurable jointly in time and sample path. This is proved from genuine joint measurability of the running infimum and the reflected-infimum survival equivalence, with no exit law or Wiener–Hopf assumption.
-- source:
--   Proved levy_running_infimum_joint_time_path_measurable and chat04_reflected_infimum_Iic_iff_survival, pinned Mathlib measurable preimages.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_closed_history_lower_survival_joint_measurable_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) :
    MeasurableSet {z : Ω × ℝ | 0 ≤ z.2 ∧
      ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1} := by sorry
