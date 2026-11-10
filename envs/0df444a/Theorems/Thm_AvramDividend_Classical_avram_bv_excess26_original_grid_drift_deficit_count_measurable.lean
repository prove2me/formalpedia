-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess26_original_grid_drift_deficit_count_measurable
-- name    : AvramDividend.Classical.avram_bv_excess26_original_grid_drift_deficit_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:18:02.716654+00:00
-- url     : https://prove2.me/theorems/b4452443-3b89-409a-a6c9-321646be9756
-- title:
--   Measurable original Lévy drift-deficient physical-cell occupancy sum
-- statement:
--   On the exact original Lévy process X, each physical-grid indicator that the source X increment is strictly below its drift increment is measurable, by Proved d55462c3 joint time-source measurability. Their finite occupied-cell count is measurable. Proved 4426d791 identifies these cells with true source negative-jump-occupied cells almost surely under finite-activity BV. This supplies the measurable surrogate needed to remove the raw Set.ncard measurability premise from the Proved physical collision L1 limit cc884bf4 and ultimately control the zero-contact E_n of 4f605d76.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess26_original_grid_drift_deficit_count_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m,
        if X.X (u (i + 1)) ω - X.X (u i) ω <
           X.drift * (((u (i + 1) - u i : ℝ≥0) : ℝ)) then
          (1 : ℝ≥0∞) else 0) := by sorry
