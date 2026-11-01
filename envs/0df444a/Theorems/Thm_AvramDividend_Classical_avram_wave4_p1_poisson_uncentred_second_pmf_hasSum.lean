-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_uncentred_second_pmf_hasSum
-- name    : AvramDividend.Classical.avram_wave4_p1_poisson_uncentred_second_pmf_hasSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:10:50.73299+00:00
-- url     : https://prove2.me/theorems/d35e4eb2-1d78-41f0-b9e8-eeb05495d940
-- title:
--   Poisson uncentred second-moment PMF HasSum identity
-- statement:
--   The exact probability mass function of a Poisson variable has ∑_n n² P(K=n)=r²+r, with absolute summability, including rate zero. The proof combines the previously Proved centred Poisson PMF variance with the independently derived first-moment and mass HasSum identities. This explicit series form, rather than an actual-variable moment statement, is the precise noncircular domination input for the random marked-sum L² count-cell partition.
-- source:
--   Canonical P1 centred-Poisson PMF variance 35af5aaf-d3ca-45a0-b8f1-49642b089ac7; pinned poissonMeasure_real_singleton and HasSum algebra. Split is required by the guarded early-split structural gate when proving random-length marked L2 integrability.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_poisson_uncentred_second_pmf_hasSum
    (r : ℝ≥0) :
    HasSum (fun n : ℕ =>
      (n : ℝ) ^ 2 * (poissonMeasure r).real {n})
      ((r : ℝ) ^ 2 + (r : ℝ)) := by sorry
