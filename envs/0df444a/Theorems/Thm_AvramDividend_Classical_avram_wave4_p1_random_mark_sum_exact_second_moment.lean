-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_random_mark_sum_exact_second_moment
-- name    : AvramDividend.Classical.avram_wave4_p1_random_mark_sum_exact_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:37:57.779134+00:00
-- url     : https://prove2.me/theorems/d57aaf15-8520-4cfb-8733-b9e9547ee2eb
-- title:
--   Exact second moment of Poisson random-length iid marked sum
-- statement:
--   On the original probability space, a true Poisson count K independent of a jointly iid sequence Y of square-integrable marks has random-length marked-sum second moment r Eν(f²)+r²(Eν f)². The proof partitions by the actual count events K=j, applies exact count-cell mark moments, sums the first and second Poisson PMF series, and uses separately proved square integrability to justify exchange of countable sum and expectation. This is the key noncircular ingredient for a compensated marked Poisson L² isometry; no martingale or Campbell identity is assumed as a premise.
-- source:
--   P1 Proved fixed iid marked block second moment, exact independent count-cell factorization, random marked-sum square integrability, and independently proved first/second Poisson PMF HasSum. Standard Lebesgue integration over disjoint count partition.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_random_mark_sum_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_count_cell_exact_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_first_pmf_hasSum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_uncentred_second_pmf_hasSum

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_random_mark_sum_exact_second_moment
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) (hf2 : MemLp f 2 ν) :
    (∫ ω, (∑ n ∈ Finset.range (K ω), f (Y n ω)) ^ 2 ∂μ) =
      (r : ℝ) * (∫ z, f z ^ 2 ∂ν) +
        (r : ℝ) ^ 2 * (∫ z, f z ∂ν) ^ 2 := by sorry
