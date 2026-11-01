-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_count_cell_exact_second_moment
-- name    : AvramDividend.Classical.avram_wave4_p1_marked_count_cell_exact_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:13:03.850031+00:00
-- url     : https://prove2.me/theorems/7106ae90-90b5-4336-a6ca-54a69046e247
-- title:
--   Exact count-cell marked Poisson second moment from count–mark independence
-- statement:
--   For an original-probability-space count K independent of the entire jointly iid mark sequence Y, the restricted expectation of the squared first-j mark block on {K=j} factors as P(K=j) times the exact fixed-block second moment j E f²+j(j-1)(Ef)². This proves the crucial conditional second-moment identity directly from independence; no compensation identity or martingale is assumed. Summing the Poisson count masses subsequently gives E S_K²=r E f²+r²(Ef)² and the compensated L² isometry.
-- source:
--   Canonically Proved P1 fixed iid block second moment f6217c9c-236e-415f-a633-244c564371f5 (only after status becomes Proved), and canonical true independent count-cell factorisation proof 75e8ec36-a3d4-45ad-a454-f39389ed1f14.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_iid_mark_fixed_sum_second_moment

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_marked_count_cell_exact_second_moment
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (j : ℕ) (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) (hf2 : MemLp f 2 ν) :
    (∫ ω in {ω | K ω = j},
      (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2 ∂μ) =
      μ.real {ω | K ω = j} *
        ((j : ℝ) * ∫ z, f z ^ 2 ∂ν +
          (j : ℝ) * ((j : ℝ) - 1) * (∫ z, f z ∂ν) ^ 2) := by sorry
