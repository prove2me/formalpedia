-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_floor_sample_mem_halfopen_cell
-- name    : AvramDividend.Classical.avram_bva20_uniform_floor_sample_mem_halfopen_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:19:02.16155+00:00
-- url     : https://prove2.me/theorems/c5b28b66-a8d3-42ef-96ee-8e6cf7296b79
-- title:
--   Exact physical uniform floor sample occupies its half-open Riemann cell
-- statement:
--   For any nonnegative physical time r and positive horizon T, the natural floor k of r(n+2)/T identifies the unique left half-open uniform grid cell. Thus r belongs to [T*k/(n+2),T*(k+1)/(n+2)). This exact deterministic membership is necessary together with previously Proved e2ccfe12 to select the source-exact frozen marked compensator coefficient in the integral 7ccc2a1a.
-- source:
--   Physical uniform floor cell membership needed for the original compensated integral step-selection bridge to theorem 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva20_uniform_floor_sample_mem_halfopen_cell
    (T : ℝ) (hT : 0 < T) (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    let k : ℕ := ⌊(r / T) * ((n : ℝ) + 2)⌋₊
    r ∈ Set.Ico
      (T * (k : ℝ) / ((n : ℝ) + 2))
      (T * ((k : ℝ) + 1) / ((n : ℝ) + 2)) := by sorry
