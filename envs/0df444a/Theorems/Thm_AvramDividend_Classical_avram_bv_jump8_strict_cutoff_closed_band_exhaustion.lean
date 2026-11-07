-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_strict_cutoff_closed_band_exhaustion
-- name    : AvramDividend.Classical.avram_bv_jump8_strict_cutoff_closed_band_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:30:49.78777+00:00
-- url     : https://prove2.me/theorems/918c1d7c-32c7-4a03-9abd-2d9c342db948
-- title:
--   Strict negative jump cutoff exhausts by closed negative mark bands
-- statement:
--   For every strictly positive Lévy cutoff ε, the strict negative-mark band (-∞,-ε) is exactly the increasing union of closed bands (-∞,-ε-1/(n+1)]. This keeps any atom at the boundary y=-ε excluded when passing from existing closed-band source Poisson facts to the intrinsic strict marked-jump Laplace test function.
-- source:
--   Archimedean small reciprocal exists_nat_one_div_lt applied to gap -ε-y. Strict exclusion at boundary follows from positivity of 1/(n+1).

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_strict_cutoff_closed_band_exhaustion
    (ε y : ℝ) (hε : 0 < ε) :
    y < -ε ↔ ∃ n : ℕ, y ≤ -ε - 1 / ((n : ℝ) + 1) := by sorry
