-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_left_limit_negation_at_positive_time
-- name    : AvramDividend.Classical.avram_wave7_01_left_limit_negation_at_positive_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:32:13.017569+00:00
-- url     : https://prove2.me/theorems/60073045-f45b-4415-abda-15010abd47f4
-- title:
--   Strict-left limit of the negated raw path equals the negated left limit at positive times
-- statement:
--   For an arbitrary real coordinate path with an established strict-left limit at positive time u, the canonical left-limit operator commutes with pointwise negation. The positive-time restriction ensures the one-sided neighbourhood filter is nontrivial.
-- source:
--   Use nhdsLT_neBot_of_exists_lt with 0<u, Tendsto.neg, and Filter.Tendsto.limUnder_eq on the canonical strict-left filter.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_left_limit_negation_at_positive_time
    (Y : ℝ≥0 → ℝ) (u : ℝ≥0) (hu : 0 < u)
    (hLeft : Tendsto Y (𝓝[<] u)
      (𝓝 (Function.leftLim Y u))) :
    Function.leftLim (fun v : ℝ≥0 => -Y v) u =
      -Function.leftLim Y u := by sorry
