-- Prove2me | Theorems.Thm_AvramDividend_Classical_raw_twoSidedFutureExit_prefix_strip
-- name    : AvramDividend.Classical.raw_twoSidedFutureExit_prefix_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:42:03.910267+00:00
-- url     : https://prove2.me/theorems/c09fbe1a-aeb5-43e1-bd05-19319fef6b8b
-- title:
--   Before an upward first passage that precedes lower exit, the path stays inside the two exit levels
-- statement:
--   For an arbitrary real-valued path g, let finite ρ be the infimum of times g exceeds upper threshold ε and suppose ρ is strictly earlier than the infimum of times g falls below ε−a. Then every path value at times r<ρ lies in the closed strip [ε−a, ε]. The statement is independent of stochastic process assumptions and is the exact pathwise prefix-band fact needed to turn q-scale two-sided exits into reflected ruin survival.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1; pathwise two-sided strict first-exit event.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.raw_twoSidedFutureExit_prefix_strip
    (g : ℝ≥0 → ℝ) (ε a : ℝ) (ρ : ℝ≥0)
    (hUp : (ρ : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : ε < g t), (t : ℝ≥0∞)))
    (hBeforeDown : (ρ : ℝ≥0∞) <
      (⨅ (t : ℝ≥0) (_ : g t < ε - a), (t : ℝ≥0∞))) :
    ∀ r : ℝ≥0, r < ρ → ε - a ≤ g r ∧ g r ≤ ε := by sorry
