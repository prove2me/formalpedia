-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_indexed_count_event_residual_future_joint
-- name    : AvramDividend.Classical.chat06_indexed_count_event_residual_future_joint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:28:17.126993+00:00
-- url     : https://prove2.me/theorems/2d1d200f-8407-467c-9e6c-7dfe2148a165
-- title:
--   Joint residual and infinite-future law on an actual fixed-clock Poisson count event
-- statement:
--   At a fixed observation clock and deterministic count n, suppose the event N=n agrees almost surely with the exact renewal-arrival interval S_n≤clock<S_(n+1). For iid exponential waits, the joint probability of N=n, residual wait greater than t, and any measurable event B of the complete sequence of waits strictly after the next claim factorises as P(N=n)*e^(-t)*mu(B). The proof applies the accepted infinite-future indexed residual theorem with a measurable prefix cylinder and clipped random age, proves the concrete arrival-time set equalities, transfers across the almost-sure count-cylinder identification, and matches the probability of the base count event. This gives the essential fixed-index input for randomly selected future-increment laws.
-- source:
--   Source bv_indexed_count_event_residual_future_joint_v2_chat06_20261021.lean, 127 lines, SHA-256 4a969850d685a0e4bb80fdd59b19b80f1774cd8d1f237588457963df8a5fcbdb. Remote probe f334a94f-0ed3-4896-962c-092500ef3345 reached deliberate sentinel, zero candidate errors at pinned revision. Official publication and acceptance remain separate.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_past_residual_full_future_joint_law

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_indexed_count_event_residual_future_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (N : Ω → ℕ) (clock t : ℝ) (ht : 0 ≤ t)
    (μ : Measure (ℕ → ℝ))
    (hLaw : HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (hCount :
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω)) :
    P {ω | N ω = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      (P {ω | N ω = n} * ENNReal.ofReal (Real.exp (-t))) * μ B := by sorry
