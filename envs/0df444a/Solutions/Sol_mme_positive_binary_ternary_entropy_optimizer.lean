-- Prove2me | solution 1 for mme_positive_binary_ternary_entropy_optimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:53:06.121529+00:00
-- url     : https://prove2.me/submissions/7095442a-41f5-43da-9afc-0e72d9943c1e

import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Real

set_option autoImplicit false

theorem solution
    (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((x / (x / (x + y))) ^ (x / (x + y)) *
        (y / (y / (x + y))) ^ (y / (x + y)) = x + y) ∧
      ((x / (x / (x + y + z))) ^ (x / (x + y + z)) *
          (y / (y / (x + y + z))) ^ (y / (x + y + z)) *
          (z / (z / (x + y + z))) ^ (z / (x + y + z)) =
        x + y + z) := by
  constructor
  · have hs : 0 < x + y := add_pos hx hy
    have hqx : x / (x / (x + y)) = x + y := by
      field_simp
    have hqy : y / (y / (x + y)) = x + y := by
      field_simp
    rw [hqx, hqy, ← Real.rpow_add hs]
    have hsum : x / (x + y) + y / (x + y) = 1 := by
      field_simp
    rw [hsum, Real.rpow_one]
  · have hs : 0 < x + y + z := add_pos (add_pos hx hy) hz
    have hqx : x / (x / (x + y + z)) = x + y + z := by
      field_simp
    have hqy : y / (y / (x + y + z)) = x + y + z := by
      field_simp
    have hqz : z / (z / (x + y + z)) = x + y + z := by
      field_simp
    rw [hqx, hqy, hqz, ← Real.rpow_add hs, ← Real.rpow_add hs]
    have hsum :
        x / (x + y + z) + y / (x + y + z) + z / (x + y + z) = 1 := by
      field_simp
    rw [hsum, Real.rpow_one]
