-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_measurable_random_grid_marked_vector_20261111
-- name    : AvramDividend.Classical.avram_a06_measurable_random_grid_marked_vector_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:10:30.029613+00:00
-- url     : https://prove2.me/theorems/cb3fbaee-bd94-41e1-b578-24951e7b6f69
-- title:
--   The full random count-grid vector of marked interval sums is measurable
-- statement:
--   Every block sum in a random natural-count grid is measurable by the random-endpoint sum lemma. Product measurability assembles the finite coordinate family; WithLp.toLp is measurable. This prepares the original random marked-grid characteristic function for rigorous pushforward and disintegration.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_measurable_random_mark_interval_20261111
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_measurable_random_grid_marked_vector_20261111
    {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω)) :
    Measurable (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
      ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) := by sorry
