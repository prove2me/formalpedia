-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_iid_fixed_count_prefix_event_residual_future_joint_from_threshold
-- name    : AvramDividend.Classical.chat06_iid_fixed_count_prefix_event_residual_future_joint_from_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:00:27.840859+00:00
-- url     : https://prove2.me/theorems/45340aeb-cc5f-434f-8d88-ca9e5affdc49
-- title:
--   Fixed-count renewal prefix event factors jointly with exponential residual survival and entire IID future suffix
-- statement:
--   Under indexed independent exponentially distributed interarrival times, a nonnegative observation clock, and the exact renewal arrival-threshold property, any measurable event Q of the first n waiting times intersected with the exact observed count N(clock)=n factors jointly with survival of the residual exponential wait for t≥0 and any measurable event of the entire future waiting-time suffix. The law is the prefix/count-event probability times exp(-t) times the specified suffix law μ(B). The proof constructs a measurable nonnegative random age from the finite prefix, converts the fixed-count event to the consecutive arrival inequalities, and applies the previously accepted indexed-IID past-residual-future joint-law theorem.
-- source:
--   bv_iid_fixed_count_prefix_event_residual_future_joint_from_threshold_chat06_20261022.lean, 121 lines, 5483 bytes, SHA-256 3a1b758f18864903470448004032df8b1db82f3a51f2e5c630a71fd56e67be35; private probe 4d7c4856-d0ed-4b40-9873-2fdb8a0d9287 reached sentinel with zero candidate errors.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat06_prefix_event_count_residual_survival_cylinder
import Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_past_residual_full_future_joint_law

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_iid_fixed_count_prefix_event_residual_future_joint_from_threshold
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (Z : Ω → (ℕ → ℝ))
    (hZ : Z = fun ω i => if h : i < n then τ i ω else 0)
    (Q : Set (ℕ → ℝ)) (hQ : MeasurableSet Q)
    (t : ℝ) (ht : 0 ≤ t)
    (μ : Measure (ℕ → ℝ))
    (hLaw : HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | (Z ω ∈ Q ∧ N ω clock = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      (P {ω | Z ω ∈ Q ∧ N ω clock = n} *
        ENNReal.ofReal (Real.exp (-t))) * μ B := by sorry
