-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_iid_mark_fixed_sum_second_moment
-- name    : AvramDividend.Classical.avram_wave4_p1_iid_mark_fixed_sum_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:00:26.854004+00:00
-- url     : https://prove2.me/theorems/f6217c9c-236e-415f-a633-244c564371f5
-- title:
--   Exact raw second moment of a fixed iid mark block
-- statement:
--   For genuinely independent identically distributed real marked amplitudes of finite second moment, the square of the sum of the first j marks has expectation j times the mark quadratic moment plus j(j-1) times the square of its mean. This exhibits the off-diagonal contribution (which becomes r² m² on Poisson randomization), and is the substantive fixed-count input for a true compound-Poisson marked L² isometry.
-- source:
--   Canonically Proved P1 iid finite mark mean and variance 25d8bb01-c0e0-4d05-b4d6-b6367b7bc05f; pinned Mathlib variance_eq_sub, memLp_finset_sum and HasLaw measurePreserving transport.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_iid_mark_finite_sum_mean_variance

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_iid_mark_fixed_sum_second_moment
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (Y : ℕ → Ω → E) (hYm : ∀ i, Measurable (Y i))
    (hYL : ∀ i, HasLaw (Y i) ν P) (hYi : iIndepFun Y P)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν)
    (hf2 : MemLp f 2 ν) (j : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range j, f (Y i ω)) ^ 2 ∂P) =
      (j : ℝ) * (∫ z, f z ^ 2 ∂ν) +
        (j : ℝ) * ((j : ℝ) - 1) * (∫ z, f z ∂ν) ^ 2 := by sorry
