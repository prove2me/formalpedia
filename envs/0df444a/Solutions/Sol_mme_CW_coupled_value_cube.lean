-- Prove2me | solution 1 for mme_CW_coupled_value_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:31:15.809074+00:00
-- url     : https://prove2.me/submissions/d65f4d1b-9de4-4389-8767-cc418059aef5

import Definitions.Def_mme_CW_coupled_value

/-!
# Cubing the coupled Coppersmith--Winograd value

This isolates the exact real-power normalization used when the paper's
symmetric value is translated to `HasSymmetricTauValueAtLeast`.  The latter
stores the cube of the displayed value as an ordinary tau-value witness for
the cyclic symmetrization.
-/

open MME

theorem solution
    (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) :
    (((2 : ℝ) ^ ((2 : ℝ) / 3) *
        (q : ℝ) ^ tau *
        (((q : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3))) ^ (3 : ℕ)) =
      4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2) := by
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hcenter : 0 ≤ (q : ℝ) ^ (3 * tau) + 2 := by positivity
  rw [mul_pow, mul_pow]
  rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 2) ((2 : ℝ) / 3) 3]
  rw [← Real.rpow_mul_natCast hq0 tau 3]
  rw [← Real.rpow_mul_natCast hcenter ((1 : ℝ) / 3) 3]
  rw [show ((2 : ℝ) / 3) * ((3 : ℕ) : ℝ) = 2 by norm_num]
  rw [show tau * ((3 : ℕ) : ℝ) = 3 * tau by ring]
  rw [show ((1 : ℝ) / 3) * ((3 : ℕ) : ℝ) = 1 by norm_num]
  rw [Real.rpow_one]
  norm_num
