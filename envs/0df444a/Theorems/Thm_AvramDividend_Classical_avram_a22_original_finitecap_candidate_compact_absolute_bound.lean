-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_finitecap_candidate_compact_absolute_bound
-- name    : AvramDividend.Classical.avram_a22_original_finitecap_candidate_compact_absolute_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:15:32.602444+00:00
-- url     : https://prove2.me/theorems/159bddbc-9f34-4129-a2dc-738476655286
-- title:
--   Original finitecap HJB candidate has finite absolute bound on compact reserve interval
-- statement:
--   Given the true HJB value candidate w continuous on the nonnegative reserve interval [0,b] for a finite dividend cap b≥0, compactness ensures a finite nonnegative K dominating |w| uniformly on that interval. This is the specific compact envelope needed to invoke the caplinear global linear-growth lemma and control original Gaussian stopped crossing increments without falsely imposing global boundedness of V.
-- source:
--   Compact original finitecap reserve interval value envelope for Gaussian stopped cap-crossing L1 dominated convergence.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_a22_original_finitecap_candidate_compact_absolute_bound
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hcont : ContinuousOn w (Icc 0 b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ,
      0 ≤ z → z ≤ b → |w z| ≤ K := by sorry
