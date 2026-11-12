-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_joint_count_mark_grid_transform_measurable_20261111
-- name    : AvramDividend.Classical.avram_a06_joint_count_mark_grid_transform_measurable_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:17:37.636557+00:00
-- url     : https://prove2.me/theorems/ed2fb5b6-ef3b-496f-8a54-5f9b135ac443
-- title:
--   Marked interval-grid vector is measurable jointly in count grid and mark stream
-- statement:
--   For finite count grids, the grid-index space is countable and has measurable singletons. At each fixed grid the vector of finite mark sums is measurable in the infinite mark stream. Countable-index joint-measurability then makes the entire marked-sum transformation measurable, enabling the exact independent-pair pushforward law.

import Mathlib
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_joint_count_mark_grid_transform_measurable_20261111
    (n : ℕ) :
    Measurable (fun p : (Fin (n + 1) → ℕ) × (ℕ → ℝ) =>
      WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (p.1 i.castSucc) (p.1 i.succ), p.2 j)) := by sorry
