-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a42_positive_taylor_small_large_energy_split
-- name    : AvramDividend.Classical.avram_ga_a42_positive_taylor_small_large_energy_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:40:27.647007+00:00
-- url     : https://prove2.me/theorems/6c81675a-ec93-4a46-977d-a091395bac8f
-- title:
--   Positive Taylor remainder quadratic energy splits into small-modulus and large-increment cost
-- statement:
--   When a nonnegative Taylor coefficient is globally bounded by M and becomes at most epsilon on displacements below delta, its quadratic energy is bounded by epsilon times total energy plus M times the large-increment energy.
-- source:
--   Direct analytic small-cell positive Taylor bridge for b0d9951c using Proved original stopped uniform quadratic energy a39 and Lindeberg large-tail a41.

import Mathlib

theorem AvramDividend.Classical.avram_ga_a42_positive_taylor_small_large_energy_split
    (a z ε M δ : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hM : a ≤ M) (hSmall : |z| < δ → a ≤ ε) :
    a * z ^ 2 ≤
      ε * z ^ 2 + M * (if δ ≤ |z| then z ^ 2 else 0) := by sorry
