-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_upper_killed_reward_tendsto
-- name    : AvramDividend.Classical.avram_root29_01_actual_upper_killed_reward_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:32:27.266657+00:00
-- url     : https://prove2.me/theorems/3c5fe04a-e501-41cd-8251-b75b67f5a293
-- title:
--   Actual upper-first killed grid-scale payoff inherits unrestricted limit
-- statement:
--   At a true positive-reserve upper-exit instant on an actual right-continuous Lévy path, with nonnegative reserve history up to the exit, every convergent sampled first-exit clock eventually has fully nonnegative continuous reserve history. Consequently the true history-killed discounted sampled q-scale reward coincides eventually with its unrestricted counterpart and inherits any verified unrestricted pathwise limit. This is the upper-first branch required to pass genuine killed-grid optional stopping to the continuous strict upper exit, without assuming the exit ratio.
-- source:
--   WS1A work/avram_root29_01_actual_upper_killed_reward_tendsto_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_upper_exit_grid_history_eventually
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_upper_terminal_positive_window

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_upper_killed_reward_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (τ : ℝ≥0) (t : ℕ → ℝ≥0)
    (ht : Tendsto t atTop (nhds τ))
    (hBefore : ∀ s : ℝ≥0, s ≤ τ → 0 ≤ x + X.X s ω)
    (hcont : ContinuousWithinAt (fun s : ℝ≥0 => X.X s ω) (Set.Ici τ) τ)
    (hpositive : 0 < x + X.X τ ω)
    (q : ℝ) (W : ℝ → ℝ) (y : ℝ)
    (hRaw : Tendsto (fun n =>
      Real.exp (-(q * (t n : ℝ))) * W (x + X.X (t n) ω))
      atTop (nhds y)) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * (t n : ℝ))) *
          W (x + X.X (t n) η)) ω) atTop (nhds y) := by sorry
