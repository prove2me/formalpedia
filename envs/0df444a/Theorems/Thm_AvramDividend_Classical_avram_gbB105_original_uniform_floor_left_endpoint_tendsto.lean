-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB105_original_uniform_floor_left_endpoint_tendsto
-- name    : AvramDividend.Classical.avram_gbB105_original_uniform_floor_left_endpoint_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:37:56.2352+00:00
-- url     : https://prove2.me/theorems/db7863bd-f9b9-4a10-aa3b-8497a63927b1
-- title:
--   Floor-selected original uniform Gaussian grid left endpoint tends to physical time
-- statement:
--   For every nonnegative physical time and positive original horizon n, the exact uniform mesh left endpoint indexed by Nat.floor(t / (n/(m+1))) tends to t as m tends to infinity. This is the direct deterministic time-index convergence used for the original B102/B65 stopped postpayment coefficient grids. It uses Proved B103 squeeze and B104 one-cell bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB103_uniform_mesh_left_approximation_squeeze
import Theorems.Thm_AvramDividend_Classical_avram_gbB104_uniform_floor_cell_gap
open Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB105_original_uniform_floor_left_endpoint_tendsto
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun m : ℕ =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
      ((⌊t / Δ⌋₊ : ℕ) : ℝ) * Δ)
      atTop (𝓝 t) := by sorry
