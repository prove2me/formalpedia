-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_singular_power_cell_bound
-- name    : AvramDividend.Classical.avram_a19_singular_power_cell_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:52:36.274703+00:00
-- url     : https://prove2.me/theorems/f4d7a827-a012-49e3-a2cb-865d414f223b
-- title:
--   Geometric surplus scale gives geometric singular HJB deficit
-- statement:
--   For positive surplus no larger than 1/16 and 1/(2^k)^2, the negative explicit singular generator profile is at least 2^k. This converts a small-surplus event into the geometric-size loss required for the A19 counterexample.
-- source:
--   A19 countermodel geometric-cell quantitative reduction, 7 November 2026.

import Mathlib.Analysis.Real.Sqrt
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_sqrt_tail_bound
noncomputable section

theorem AvramDividend.Classical.avram_a19_singular_power_cell_bound
    (k : Nat) (y : Real) (hy : 0 < y)
    (hsmall : y <= 1 / 16)
    (hpower : y <= 1 / ((2 : Real) ^ k) ^ 2) :
    (2 : Real) ^ k <=
      -(3 + y - 4 * Real.sqrt y - 2 / Real.sqrt y) := by sorry
