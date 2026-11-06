-- Prove2me | solution 1 for isBigO_pow_pow_of_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:36.106197+00:00
-- url     : https://prove2.me/submissions/e9513974-ebe3-49b3-a9f0-1e625ba539a1

import Mathlib.NumberTheory.LSeries.PrimesInAP

open Asymptotics Filter

theorem solution {m n : ℕ} (h : m ≤ n) :
    (fun x : ℝ => x ^ m) =O[atTop] (fun x : ℝ => x ^ n) := by
  rcases h.eq_or_lt with rfl | h
  · exact isBigO_refl _ _
  · exact (isLittleO_pow_pow_atTop_of_lt h).isBigO
