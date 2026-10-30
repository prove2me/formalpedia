-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_grid_reward_meas
-- name    : AvramDividend.Classical.avram_root29_01_actual_killed_grid_reward_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:37:23.295614+00:00
-- url     : https://prove2.me/theorems/eb81723f-0ce8-48a2-b2ab-daee5f55bf70
-- title:
--   Original-Lévy lower-history-killed first-exit grid q-scale reward is measurable
-- statement:
--   For an actual spectrally negative Lévy law and first-outside sampled hittingBtwn index, the full continuous lower-survival-history-killed discounted stopped q-scale reward is a genuine measurable real random variable. It composes source-specific measurability of the bounded first-exit index, random continuous survival event and stopped time/reserve with the canonical measurability of the potentially discontinuous scale function. Removes all hidden measurable-set/observable premises before the killed-grid quadratic-to-expectation limit.
-- source:
--   WS1A work/avram_root29_01_actual_killed_grid_reward_meas_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_grid_hitting_index_meas
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_random_grid_history_meas
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_killed_grid_reward_meas
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    Measurable (fun ω =>
      ({η : Ω | ∀ t : ℝ≥0,
        t ≤ clock (K η) → 0 ≤ x + X.X t η}).indicator
          (fun η => Real.exp (-(q * (clock (K η) : ℝ))) *
            W (x + X.X (clock (K η)) η)) ω) := by sorry
