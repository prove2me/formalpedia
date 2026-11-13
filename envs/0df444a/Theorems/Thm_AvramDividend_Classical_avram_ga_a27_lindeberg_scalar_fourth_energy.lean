-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a27_lindeberg_scalar_fourth_energy
-- name    : AvramDividend.Classical.avram_ga_a27_lindeberg_scalar_fourth_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:43:35.067823+00:00
-- url     : https://prove2.me/theorems/e1ca225d-e541-4c3c-bca4-b69926750929
-- title:
--   Large Gaussian increment quadratic energy is bounded by fourth energy
-- statement:
--   For any positive threshold, the quadratic energy of a real increment above the threshold is bounded by its fourth power divided by the squared threshold.
-- source:
--   Gaussian A positive-only interior Taylor Lindeberg bound, mission 1300fbe7, supporting b0d9951c; source-independent scalar estimate.

import Mathlib

theorem AvramDividend.Classical.avram_ga_a27_lindeberg_scalar_fourth_energy (r z : ℝ) (hr : 0 < r) :
    (if r ≤ |z| then z ^ 2 else 0) ≤ z ^ 4 / r ^ 2 := by sorry
