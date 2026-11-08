-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_singular_weighted_series_not_summable
-- name    : AvramDividend.Classical.avram_a19_singular_weighted_series_not_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:15:30.672352+00:00
-- url     : https://prove2.me/theorems/013b853b-e233-4099-a002-a9835f98964f
-- title:
--   Near-zero singular generator weighted series diverges
-- statement:
--   If the post-dividend surplus in cell k lies below the dyadic square scale, the explicit singular generator deficit is at least 2^k. After geometric probability weighting by 2^-k, the terms are at least one, so their real series is not summable. This is the countable-law obstruction needed for the original A19 generator-cell countermodel.
-- source:
--   A19 source-exact generator-cell disproof research, 7 November 2026; depends on proved power-cell bound f4d7a827.

import Mathlib.Analysis.Real.Sqrt
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_power_cell_bound
noncomputable section

theorem AvramDividend.Classical.avram_a19_singular_weighted_series_not_summable
    (y : Nat -> Real)
    (hy : forall k, 0 < y k)
    (hsmall : forall k, y k <= 1 / 16)
    (hpower : forall k, y k <= 1 / ((2 : Real) ^ k) ^ 2) :
    Not (Summable (fun k : Nat =>
      (-(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))) /
        (2 : Real) ^ k)) := by sorry
