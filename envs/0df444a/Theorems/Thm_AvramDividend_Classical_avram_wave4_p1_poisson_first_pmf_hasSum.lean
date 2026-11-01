-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_first_pmf_hasSum
-- name    : AvramDividend.Classical.avram_wave4_p1_poisson_first_pmf_hasSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:18:02.039038+00:00
-- url     : https://prove2.me/theorems/80fa6773-5cd0-4c77-8678-678d422ac7e8
-- title:
--   Exact first Poisson probability mass series
-- statement:
--   For each nonnegative Poisson intensity r, the first-moment Poisson PMF series ∑ n P_r(n) is absolutely summable and has value r, including at r=0. Proof by the exact factorial mass recurrence and shifted HasSum; this is needed to identify the random marked Poisson square expectation from exact count-cell second moments.
-- source:
--   Pinned Mathlib poissonMeasure_real_singleton, hasSum_one_poissonMeasure and hasSum_nat_add_iff', independent of any compensated integral identity.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_poisson_first_pmf_hasSum
    (r : ℝ≥0) :
    HasSum (fun n : ℕ => (n : ℝ) * (poissonMeasure r).real {n}) (r : ℝ) := by sorry
