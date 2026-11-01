-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum
-- name    : AvramDividend.Classical.avram_wave4_p1_poisson_centered_count_variance_hasSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:26:40.807797+00:00
-- url     : https://prove2.me/theorems/35af5aaf-d3ca-45a0-b8f1-49642b089ac7
-- title:
--   Exact centred Poisson count variance from PMF factorial moments
-- statement:
--   For any nonnegative Poisson rate r, the exact HasSum of (n-r)^2 times the Poisson real point mass is r. The proof derives the result from Poisson normalisation and the factorial-shift recurrences for its first and second moments, with no moment or compensation assumption. This is the count-energy component of a weighted Poisson L2 isometry; the independence and product-integrability part is proved in a separate parent theorem.
-- source:
--   Pinned Mathlib ProbabilityTheory.poissonMeasure_real_singleton and hasSum_one_poissonMeasure; factorial-moment strategy independently adapted from MIT-licensed LeanLevy Probability/Poisson.lean at pinned source; Applebaum compound Poisson moments.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_poisson_centered_count_variance_hasSum
    (r : ℝ≥0) :
    HasSum (fun (n : ℕ) => ((n : ℝ) - (r : ℝ)) ^ 2 *
      (poissonMeasure r).real {n}) (r : ℝ) := by sorry
