-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_count_second_moment_integrable
-- name    : AvramDividend.Classical.avram_wave4_p1_poisson_count_second_moment_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:54:03.541436+00:00
-- url     : https://prove2.me/theorems/61b5ca3a-d170-4262-814e-23db2d5f9e1b
-- title:
--   True Poisson random count has finite uncentred second moment
-- statement:
--   An actual measurable integer-valued random variable K on a probability space with Poisson(r) law has an integrable square and E[K²]=r²+r, for every nonnegative rate including zero. The proof derives this from the PMF factorial/centred moments, not an assumed moment identity. The result supplies the count-second-moment bound needed to turn exact-count marked L2 estimates into unbounded compound-Poisson L2 integrability.
-- source:
--   Canonically Proved P1 Poisson centred count PMF variance 35af5aaf-d3ca-45a0-b8f1-49642b089ac7; exact pinned poissonMeasure_real_singleton, HasSum arithmetic, integrable_poissonMeasure_iff and HasLaw integral transport.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_poisson_count_second_moment_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) P) :
    Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
      (∫ ω, (K ω : ℝ) ^ 2 ∂P) = (r : ℝ) ^ 2 + (r : ℝ) := by sorry
