-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_count_cell_l2_bound
-- name    : AvramDividend.Classical.avram_wave4_p1_marked_count_cell_l2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:52:37.386237+00:00
-- url     : https://prove2.me/theorems/02f2486f-3ccc-4fa2-ba5c-75502e08ec12
-- title:
--   Exact Poisson count-cell quadratic bound for independent L2 marks
-- statement:
--   For an actual probability-space random count independent of its entire mark sequence, with identically distributed square-integrable real mark amplitudes, the expected squared sum of the first j marks restricted to {K=j} is at most P(K=j) times j squared times the common mark energy. This provides a noncircular finite-rate L2 domination input; it neither assumes a martingale/isometry nor treats the original Levy source jump law.
-- source:
--   Pinned Mathlib sq_sum_le_card_mul_sum_sq, memLp_finset_sum, memLp_two_iff_integrable_sq, and canonically Proved true count-cell mark expectation 75e8ec36-a3d4-45ad-a454-f39389ed1f14.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_independent_count_cell_mark_mean_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_marked_count_cell_l2_bound
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (f : E → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 ν)
    (j : ℕ) :
    (∫ ω in {ω | K ω = j},
      (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2 ∂μ) ≤
      μ.real {ω | K ω = j} *
        ((j : ℝ) ^ 2 * ∫ z, f z ^ 2 ∂ν) := by sorry
