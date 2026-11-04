-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_strict_left_limit_at_zero_is_vacuous
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_strict_left_limit_at_zero_is_vacuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:45:15.643974+00:00
-- url     : https://prove2.me/theorems/32b1a995-bac3-41d6-9670-180dc0a6098e
-- title:
--   At time zero the nonnegative-time strict-left path limit is vacuous
-- statement:
--   Because the nonnegative real line contains no time strictly below zero, the left-sided neighbourhood filter there is bottom, and any function trivially tends to its canonical Function.leftLim at zero. This joins source cadlag hypotheses on strictly positive times with all-time deterministic grid convergence.

import Mathlib

namespace AvramDividend.Classical
end AvramDividend.Classical

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_strict_left_limit_at_zero_is_vacuous (Y : ℝ≥0 → ℝ) :
    Tendsto Y (𝓝[<] (0 : ℝ≥0))
      (𝓝 (Function.leftLim Y 0)) := by sorry
