-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b77_original_true_stop_min_grid_stopping_times
-- name    : AvramDividend.Classical.avram_b77_original_true_stop_min_grid_stopping_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:58:30.638306+00:00
-- url     : https://prove2.me/theorems/913ae885-54c9-4caf-967d-577d13dfd009
-- title:
--   Original actual physical stopping-time grid minimum with clipped clock preserves stopping times
-- statement:
--   For the genuine original ruin-clipped stopping clock kappa and any deterministic nonnegative grid u_i, each min(u_i,kappa) is a stopping time for the same right-continuous filtration. Supplies exact stopped-grid measurability and stopping-time hypotheses for B74 and B75 without anticipative rounding.
-- source:
--   Pinned Mathlib 0df444a3 theorem MeasureTheory.IsStoppingTime.min_const and WithTop.coe_min, verified in original Prove2Me premise index.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b77_original_true_stop_min_grid_stopping_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (κ : Ω → ℝ≥0)
    (hκstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (κ ω : WithTop ℝ≥0)))
    (u : ℕ → ℝ≥0) :
    ∀ i : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => ((min (u i) (κ ω) : ℝ≥0) : WithTop ℝ≥0)) := by sorry
