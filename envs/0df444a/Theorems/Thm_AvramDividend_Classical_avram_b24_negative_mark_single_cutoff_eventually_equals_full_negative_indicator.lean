-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_negative_mark_single_cutoff_eventually_equals_full_negative_indicator
-- name    : AvramDividend.Classical.avram_b24_negative_mark_single_cutoff_eventually_equals_full_negative_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:56:43.155059+00:00
-- url     : https://prove2.me/theorems/8058318a-c01f-4eb3-b2cd-5668a79c9b83
-- title:
--   A single original finite-activity negative-mark reciprocal cutoff indicator eventually equals the true small-negative mark indicator
-- statement:
--   For any actual negative-mark amplitude z from the original Lévy source, the finite cutoff indicator (-1<z≤-1/(n+1)) eventually agrees with the full untruncated small-negative indicator (-1<z<0) for all sufficiently fine cutoffs. This is exact for every fixed z, including zero and marks at the -1 boundary. A separate finite-set sum lemma combines the finitely many events without an excessively large proof and establishes the original finite-activity smallmark physical source identity.
-- source:
--   Pinned reciprocal convergence and comparison of the three real mark regions.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_negative_mark_single_cutoff_eventually_equals_full_negative_indicator
    (z : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (if -1 < z ∧ z ≤ -(1 / ((n : ℝ) + 1)) then z else 0) =
      (if -1 < z ∧ z < 0 then z else 0) := by sorry
