-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_compound_poisson_centered_l2_isometry
-- name    : AvramDividend.Classical.avram_wave4_p1_compound_poisson_centered_l2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:51:07.582824+00:00
-- url     : https://prove2.me/theorems/12d688ee-f884-4081-a177-023710648191
-- title:
--   Noncircular compensated iid marked-Poisson L² isometry
-- statement:
--   For a genuine Poisson count K of intensity r independent of an entire jointly iid marked sequence Y on the original probability space, and a measurable square-integrable mark kernel f, the centred actual marked sum has mean-square r Eν(f²). This is a true compensated marked-Poisson isometry derived from exact raw moments and Campbell expectation, not a martingale or compensator premise; time-dependent predictable coefficients and stopping require further independent increments.
-- source:
--   Canonically Proved WS1B exact random-mark sum L1 and Campbell expectation, and P1 genuine global marked L2 and raw second-moment identities (these must be Proved before proof upload).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_random_mark_sum_exact_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_random_mark_sum_square_integrable
import Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_integrable_ws01b
import Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_campbell_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_compound_poisson_centered_l2_isometry
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
    (∫ ω, ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν) ^ 2 ∂μ) =
      (r : ℝ) * ∫ z, f z ^ 2 ∂ν := by sorry
