-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_floor_index_within_inner_row
-- name    : AvramDividend.Classical.avram_bva20_uniform_floor_index_within_inner_row
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:22:16.649203+00:00
-- url     : https://prove2.me/theorems/8c25168c-d1b8-4d85-aa28-b999e035212a
-- title:
--   Physical uniform floor index belongs to the strict inner horizon row
-- statement:
--   For positive T and nonnegative r strictly before the last uniform-grid endpoint T(n+1)/(n+2), the natural floor of r(n+2)/T is less than n+1. It is a valid coefficient index in the original finite marked-compensator Riemann sum. Necessary with Proved step-cell selection and floor-cell membership in proving 7ccc2a1a.
-- source:
--   Exact finite row index bridge for physical stopped compensator Riemann approximation 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva20_uniform_floor_index_within_inner_row
    (T : ℝ) (hT : 0 < T) (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r)
    (hrT : r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)) :
    ⌊(r / T) * ((n : ℝ) + 2)⌋₊ < n + 1 := by sorry
