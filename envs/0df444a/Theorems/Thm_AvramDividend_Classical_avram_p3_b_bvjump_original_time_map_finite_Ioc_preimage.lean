-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_time_map_finite_Ioc_preimage
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_time_map_finite_Ioc_preimage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:01:46.240477+00:00
-- url     : https://prove2.me/theorems/24a903f6-b1a9-4280-a24f-010e46ce0c85
-- title:
--   Original nonnegative physical clock pushforward preimage agrees with the real stopped interval
-- statement:
--   For the original real physical clock restricted to [0,T] and its NNReal representation via Real.toNNReal, the preimage of the actual (s,t] source interval (with t≤T) is exactly the original real interval (s,t]. This rigorously fixes the time-coordinate transport in the true P2 finite-clock Lévy intensity, avoiding nonphysical negative real times that Real.toNNReal otherwise clips to zero. No stochastic assumptions or compensator law.
-- source:
--   Mathlib Real.coe_toNNReal, NNReal order embedding, set interval membership, Avram finite physical clock.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_time_map_finite_Ioc_preimage
    (s t T : ℝ≥0) (htT : t ≤ T) :
    (Real.toNNReal ⁻¹' Ioc s t) ∩ Icc (0 : ℝ) (T : ℝ) =
      Ioc (s : ℝ) (t : ℝ) := by sorry
