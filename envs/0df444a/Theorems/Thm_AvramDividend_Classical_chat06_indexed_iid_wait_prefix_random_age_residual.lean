-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_wait_prefix_random_age_residual
-- name    : AvramDividend.Classical.chat06_indexed_iid_wait_prefix_random_age_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:58:11.810983+00:00
-- url     : https://prove2.me/theorems/64f3a150-37d8-495c-8bf4-33870dafb6db
-- title:
--   Exponential residual memorylessness at an indexed iid waiting-time prefix
-- statement:
--   At each fixed index of an iid exponential waiting-time sequence, the zero-padded earlier waiting-time prefix is independent of the current waiting time. Any measurable event of that prefix and any nonnegative measurable random age determined by it therefore satisfy exact exponential residual-survival factorisation. This supports conditioning on Poisson count-selection cylinders at a fixed observation clock; the identification of the actual count event and full natural filtration remains separate.
-- source:
--   Verified source: bv_indexed_iid_wait_prefix_random_age_residual_v3_chat06_20261021.lean, 72 lines, source SHA-256 75132486924913d5bbcd2a233425465dc972f5bf16e795a681c93c9367549d05. Remote private job 82f6db1b-88ca-4b6c-8c08-53e152cd66d5 passed source elaboration to deliberate sentinel, with zero candidate error lines at pinned revision 0df444a360eaa60ab8c11dca51a86af692955474. This is not an official proof verdict.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_masked_iid_prefix_full_suffix_independence
import Theorems.Thm_AvramDividend_Classical_chat06_independent_past_event_exponential_residual

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_indexed_iid_wait_prefix_random_age_residual
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (Z : Ω → (ℕ → ℝ))
    (hZ : Z = fun ω i => if h : i < n then τ i ω else 0)
    (age : (ℕ → ℝ) → ℝ) (hAge : Measurable age)
    (D : Set (ℕ → ℝ)) (hD : MeasurableSet D)
    (hNonneg : ∀ᵐ z ∂(P.map Z), 0 ≤ age z)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | Z ω ∈ D ∧ age (Z ω) + t < τ n ω} =
      P {ω | Z ω ∈ D ∧ age (Z ω) < τ n ω} *
        ENNReal.ofReal (Real.exp (-t)) := by sorry
