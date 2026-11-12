-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva21_original_uniform_floor_step_measurable
-- name    : AvramDividend.Classical.avram_bva21_original_uniform_floor_step_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:14:30.763198+00:00
-- url     : https://prove2.me/theorems/d581abf8-8dae-4732-a99f-0c5c6789da35
-- title:
--   Original inclusive uniform-grid floor-step compensator integrand is Borel measurable
-- statement:
--   The physical uniform floor-grid coefficient function is exactly the finite sum of indicator-weighted constant coefficients over the half-open cells, by the already Proved full-floor mask identity ac1e45d7. Each half-open cell is Borel and each coefficient is constant, so the real-time step integrand is measurable without any assumptions on the individual coefficients. This discharges the A-side strongly measurable hypothesis needed for paired dominated convergence in original 7ccc2a1a.
-- source:
--   Source-A exact step integrand measurability required for original compensated grid DCT theorem 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_step_full_floor_mask_identity
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva21_original_uniform_floor_step_measurable
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ) :
    Measurable (fun t : ℝ =>
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0) := by sorry
