-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a132_real_rate_over_n_void_bound_rescaling_20261114
-- name    : AvramDividend.Classical.avram_a132_real_rate_over_n_void_bound_rescaling_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T19:45:31.754117+00:00
-- url     : https://prove2.me/theorems/aa8e93a9-8ffc-4d63-bd5c-62b775892377
-- title:
--   Scale the first-two-factorial-moment void-probability inequalities from small time 1/n to fixed rate
-- statement:
--   Pure algebra: for positive integer n, if a real q lies between r/n−(r/n)² and r/n, then n q lies between r−r²/n and r. Intended to keep the stochastic small-time Lévy Borel void intensity proof below the Prove2Me theorem complexity gate.
-- source:
--   Field inversion n>0, mul_le_mul_of_nonneg_left, ring. No stochastic inputs or private theorem imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_a132_real_rate_over_n_void_bound_rescaling_20261114
    (r q : ℝ) (n : ℕ) (hn : 0 < n)
    (hLo : r / (n : ℝ) - (r / (n : ℝ)) ^ 2 ≤ q)
    (hHi : q ≤ r / (n : ℝ)) :
    r - r ^ 2 / (n : ℝ) ≤ (n : ℝ) * q ∧
      (n : ℝ) * q ≤ r := by sorry
