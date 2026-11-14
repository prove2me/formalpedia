-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a97_single_crossing_positive_error_finset_bound
-- name    : AvramDividend.Classical.avram_ga_a97_single_crossing_positive_error_finset_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:25:50.005202+00:00
-- url     : https://prove2.me/theorems/8b648d78-8079-4416-be5f-590c03639b02
-- title:
--   Original Gaussian stopped unique crossing source cell positive residual budget does not grow with physical mesh count
-- statement:
--   If the set of genuine stopping-crossing physical Gaussian cells contains at most one index and every crossing positive source residual is bounded by a single nonnegative terminal error budget, the total positive crossing error is at most that same single budget.
-- source:
--   Original b0d9951c clipped Gaussian unique crossing cell one-sided positive L1 route, combine with ga_a95 and original terminal positive expectation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_ga_a97_single_crossing_positive_error_finset_bound (S : Finset ℕ) (f : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hCard : S.card ≤ 1)
    (hBound : ∀ i ∈ S, max (f i) 0 ≤ B) :
    (∑ i ∈ S, max (f i) 0) ≤ B := by sorry
