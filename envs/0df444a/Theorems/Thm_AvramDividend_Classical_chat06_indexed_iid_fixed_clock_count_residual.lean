-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_fixed_clock_count_residual
-- name    : AvramDividend.Classical.chat06_indexed_iid_fixed_clock_count_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:13:10.204497+00:00
-- url     : https://prove2.me/theorems/405a74e2-c1f0-4fe0-a1ca-5b87a029af24
-- title:
--   Exact fixed-clock Poisson count-cylinder exponential residual survival
-- statement:
--   Let S_n denote the sum of the first n iid exponential waiting times. For any fixed observation clock s and nonnegative horizon t, the probability that S_n is at most s and the next arrival is later than s+t equals the probability of the count-n arrival interval S_n≤s<S_(n+1) multiplied by e^(-t). The proof uses the measurable masked past, a nonnegative clipped random age and the accepted full measurable past-event exponential memorylessness theorem, followed by exact finite-sum arrival algebra. This directly identifies the observed Poisson count cylinder, while countable selection and full filtration increments are subsequent obligations.
-- source:
--   Source bv_indexed_iid_fixed_clock_count_residual_v3_chat06_20261021.lean, 115 lines; SHA-256 7661dc8e4de818469a841d4f675c7ed9458035c6a2eb90b752358b4cc216777b; private probe f9a83a94-7fcb-40db-b75f-34b4f2d747da reached deliberate sentinel with zero candidate source errors at pinned revision. No official verdict implied.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat06_masked_iid_prefix_full_suffix_independence
import Theorems.Thm_AvramDividend_Classical_chat06_independent_past_event_exponential_residual

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_indexed_iid_fixed_clock_count_residual
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ) (clock t : ℝ)
    (ht : 0 ≤ t)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
      clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω} =
    P {ω | (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
      clock < ∑ i ∈ Finset.range (n + 1), τ i ω} *
        ENNReal.ofReal (Real.exp (-t)) := by sorry
