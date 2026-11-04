-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_support_has_band
-- name    : AvramDividend.Classical.avram_p2_j_ui_compact_negative_support_has_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:51:05.484221+00:00
-- url     : https://prove2.me/theorems/21e67ce9-b8ea-4bea-a5f0-142ef58a8d49
-- title:
--   Compact strictly negative topological support yields quantitative two-sided support cutoffs
-- statement:
--   For a genuine real test function whose topological support is compact and contained in the strictly negative half-line, construct a real lower cutoff and strictly positive epsilon such that the test vanishes below the lower cutoff and above -epsilon. This supplies the exact source support hypotheses of the already-Proved original negative-test Lévy rate, including the empty-support case.

import Mathlib.Data.Real.Basic
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact

open Set

theorem AvramDividend.Classical.avram_p2_j_ui_compact_negative_support_has_band
    (g : ℝ → ℝ)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    ∃ a ε : ℝ, 0 < ε ∧
      (∀ y : ℝ, y < a → g y = 0) ∧
      (∀ y : ℝ, -ε < y → g y = 0) := by sorry
