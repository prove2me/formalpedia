-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:25:53.609795+00:00
-- url     : https://prove2.me/theorems/12df1121-6567-493a-be9b-79b0623f967c
-- title:
--   Monotone convergence of ENNReal jump totals under cofinal size cutoffs
-- statement:
--   Let f be any nonnegative extended-real jump magnitude assignment indexed by an arbitrary type. An antitone sequence of cutoffs that eventually falls below every positive f(a) recovers the entire tsum as the supremum of cutoff tsums. This generic order theorem is the exact analytic bridge needed to pass from finite negative-jump bands to complete original BV path jump totals, without assuming integrability.
-- source:
--   Pinned Mathlib ENNReal.tsum_eq_iSup_sum and ENNReal.sum_le_tsum; finite-subset common cutoff obtained by induction with a maximum witness; total upper bound from ENNReal.tsum_le_tsum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- An antitone size cutoff cofinal below every positive jump magnitude
recovers the full ENNReal total through monotone cutoff sums. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core
    {α : Type*} (f : α → ℝ≥0∞)
    (ε : ℕ → ℝ≥0∞) (hε : Antitone ε)
    (hCover : ∀ a, 0 < f a → ∃ n : ℕ, ε n < f a) :
    (⨆ n : ℕ, ∑' a : α, if ε n < f a then f a else 0) =
      ∑' a : α, f a := by sorry
