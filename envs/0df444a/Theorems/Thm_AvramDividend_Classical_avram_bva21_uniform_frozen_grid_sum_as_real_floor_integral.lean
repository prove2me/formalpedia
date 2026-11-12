-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva21_uniform_frozen_grid_sum_as_real_floor_integral
-- name    : AvramDividend.Classical.avram_bva21_uniform_frozen_grid_sum_as_real_floor_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:58:54.739044+00:00
-- url     : https://prove2.me/theorems/b0b843ab-bb2b-4f0b-be72-4d198ec645e4
-- title:
--   Exact inclusive uniform Riemann sum equals its full real-time floor-cell integral
-- statement:
--   For the original inclusive uniform grid with n+1 cells of width T/(n+2), the full sum of frozen coefficients is precisely the real Lebesgue integral of the piecewise constant coefficient at physical floor index floor(t(n+2)/T), masked to the actual union of cells [0,T(n+1)/(n+2)). Assemble two previously Proved tools: the exact frozen-grid step integral and the physical full-floor mask identity. This is the source-A representation necessary for proving 7ccc2a1a.
-- source:
--   Necessary exact original inclusive A-compensator Riemann-sum time-integral representation for 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_frozen_grid_sum_as_step_integral
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_step_full_floor_mask_identity
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva21_uniform_frozen_grid_sum_as_real_floor_integral
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1),
      (T / ((n : ℝ) + 2)) * c i) =
    ∫ t : ℝ,
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0 := by sorry
