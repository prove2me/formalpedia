-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB34_sigma1_upper_band_positive_drift
-- name    : AvramDividend.Classical.avram_gbB34_sigma1_upper_band_positive_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:16:16.782959+00:00
-- url     : https://prove2.me/theorems/70ac0699-7b60-4677-8a51-77c57fb92b20
-- title:
--   Positive unit-Gaussian strip drift and bounded terminal cap defect
-- statement:
--   For the explicit positive-drift unit-Gaussian countermodel candidate with cap 1/8 and cutoff 5/44, prove the affine upper-strip generator has a uniform positive lower bound while the terminal quadratic cap defect lies between zero and 1/1936. This is a deterministic supporting lemma only, not a counterexample to the stochastic theorem.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gbB34_sigma1_upper_band_positive_drift
  (y : ℝ) (hylo : (5 / 44 : ℝ) ≤ y)
  (hyhi : y ≤ (1 / 8 : ℝ)) :
  (193419 / 96800 : ℝ) ≤ 2 - (1 / 100 : ℝ) * (y + 15 / 242) ∧
  0 ≤ y - 4 * y ^ 2 - 15 / 242 ∧
  y - 4 * y ^ 2 - 15 / 242 ≤ (1 / 1936 : ℝ) := by sorry
