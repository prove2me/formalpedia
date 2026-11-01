-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_random_mark_sum_square_integrable
-- name    : AvramDividend.Classical.avram_wave4_p1_poisson_random_mark_sum_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:06:35.302308+00:00
-- url     : https://prove2.me/theorems/bff66e88-dbe9-4837-b3e6-97b5aade88a0
-- title:
--   Unbounded random-length marked Poisson sum is truly square integrable
-- statement:
--   Under the genuine Poisson(r) law for the random count and independence of that count from the entire identically-law mark sequence, a square-integrable real mark amplitude yields an integrable square of the random-length compound-Poisson sum. No iid hypothesis is required for this L2 domination. The proof bounds each exact-count cell quadratically by P(K=j) j² E f², sums those bounds using the actual Poisson second moment, and applies the integrableOn countable partition theorem. It does not assume the desired L2 moment or martingale property.
-- source:
--   Canonical Proved P1 exact-count marked L2 bound 02f2486f-3ccc-4fa2-ba5c-75502e08ec12 (only when Proved), and P1 PMF centred variance 35af5aaf-d3ca-45a0-b8f1-49642b089ac7; pinned integrableOn_iUnion_of_summable_integral_norm.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_count_cell_l2_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_poisson_random_mark_sum_square_integrable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (f : E → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 ν) :
    Integrable (fun ω =>
      (∑ n ∈ Finset.range (K ω), f (Y n ω)) ^ 2) μ := by sorry
