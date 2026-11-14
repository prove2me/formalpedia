-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a83_original_gaussian_uniform_mesh_time_mass_le_horizon
-- name    : AvramDividend.Classical.avram_ga_a83_original_gaussian_uniform_mesh_time_mass_le_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:53:14.155917+00:00
-- url     : https://prove2.me/theorems/c613e888-72d5-40df-b0bd-ebd9c5365a25
-- title:
--   Actual original Gaussian uniform physical mesh m cells occupy no more than finite source horizon n
-- statement:
--   For any natural source horizon n and physical mesh index m, the product of m by the genuine nonnegative uniform width n/(m+1), cast to the real physical clock, is at most n.
-- source:
--   Direct genuine source Gaussian physical mesh hMass condition in ga_a82, needed for ga_a81 stopped cross L1 and b0d9951c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a83_original_gaussian_uniform_mesh_time_mass_le_horizon (n m : ℕ) :
    (m : ℝ) *
      (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) ≤
        (n : ℝ) := by sorry
