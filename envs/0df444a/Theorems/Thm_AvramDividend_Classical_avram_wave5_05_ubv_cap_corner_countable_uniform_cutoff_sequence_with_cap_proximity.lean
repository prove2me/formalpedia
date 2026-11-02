-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_countable_uniform_cutoff_sequence_with_cap_proximity
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_countable_uniform_cutoff_sequence_with_cap_proximity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:21:53.398197+00:00
-- url     : https://prove2.me/theorems/6074cc01-ba22-43b9-9956-11ce26dbdf08
-- title:
--   Countable UBV slope-one cutoffs uniformly approximate cap continuation while their kink locations approach the cap at a quantified rate
-- statement:
--   Under positive finite cap, continuous w on nonnegative states, strictly interior C² and w'≥1, there is a countable family of locations b_n in (0,c) with explicit gap c−b_n<1/(n+1). Simultaneously, the true slope-one cap continuation f_c and every interior cutoff f_{b_n} satisfy 0≤f_c(y)−f_{b_n}(y)<1/(n+1) for all y≥0. Thus both kink locations and value approximants converge to the actual cap without assuming a finite left derivative or global C². This is a deterministic stochastic-boundary localisation prerequisite, not an Itô formula or cap Stieltjes correction.
-- source:
--   Parent Proved cap-proximity ε cutoff target 7dcce965-49e9-4aec-9e57-1f0f35d359b3 (submit before publishing this dependent target). Corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706 stays unchanged.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_with_cap_proximity

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_countable_uniform_cutoff_sequence_with_cap_proximity
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y) :
    ∃ b : ℕ → ℝ,
      (∀ n : ℕ, 0 < b n ∧ b n < c ∧
        c - b n < 1 / ((n : ℝ) + 1)) ∧
      ∀ (n : ℕ) (y : ℝ), 0 ≤ y →
        0 ≤ (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) ∧
        (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) <
          1 / ((n : ℝ) + 1) := by sorry
