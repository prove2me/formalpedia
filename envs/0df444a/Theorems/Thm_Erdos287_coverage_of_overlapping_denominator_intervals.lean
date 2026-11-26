-- Prove2me | Theorems.Thm_Erdos287_coverage_of_overlapping_denominator_intervals
-- name    : Erdos287.coverage_of_overlapping_denominator_intervals
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:45:29.232557+00:00
-- url     : https://prove2.me/theorems/3640106b-9857-5cb1-b998-39b04ea17b49
-- title:
--   Adjacent-pair coverage across overlapping denominator intervals
-- statement:
--   Let $D,E$ cover adjacent pairs in their respective integer intervals. If the intervals overlap, then every adjacent pair in the combined interval has a member in $D\cup E$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.coverage_of_overlapping_denominator_intervals (D E : Finset ℕ) (a b c d : ℕ) (hacross : a ≤ d) (hccross : c ≤ b)
    (hD : ∀ x, a ≤ x → x + 1 ≤ b → x ∈ D ∨ x + 1 ∈ D)
    (hE : ∀ x, c ≤ x → x + 1 ≤ d → x ∈ E ∨ x + 1 ∈ E) :
    ∀ x, min a c ≤ x → x + 1 ≤ max b d → x ∈ D ∪ E ∨ x + 1 ∈ D ∪ E := by sorry
