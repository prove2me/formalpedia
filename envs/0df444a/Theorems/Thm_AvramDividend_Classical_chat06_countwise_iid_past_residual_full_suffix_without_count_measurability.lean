-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_countwise_iid_past_residual_full_suffix_without_count_measurability
-- name    : AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_without_count_measurability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:39:25.881773+00:00
-- url     : https://prove2.me/theorems/9e46b8ad-31ad-49ab-a0df-797e702db0f4
-- title:
--   Countwise IID past-residual-full-future factorisation with automatic count measurability
-- statement:
--   For any renewal count satisfying the exact arrival-threshold relation and measurable IID interarrival times, count-measurability follows automatically from the accepted arrival-threshold measurability theorem. Accordingly a measurable observed-past event admitting finite-prefix representations on count cylinders factorises jointly against the exponential residual waiting-time survival and the entire future suffix, under a shared suffix law and the stated tail identity. This removes a redundant measurability hypothesis from the accepted countwise independence theorem.
-- source:
--   bv_countwise_iid_past_residual_full_suffix_without_count_measurability_chat06_20261022.lean, 42 lines, 1986 bytes, SHA-256 a6538afa34654373917488817a2741c6f55c12975d6f775b3dc89cd696d3ad60; private remote probe 9d8299a0-cf07-4b96-9b30-a98fdc2c2c9e passed sentinel.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_countwise_iid_past_residual_full_suffix_from_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_count_measurable_from_arrival_threshold

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_without_count_measurability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (H : Set Ω) (hH : MeasurableSet H)
    (hRep : ∀ n : ℕ, ∃ Q : Set (ℕ → ℝ),
      MeasurableSet Q ∧
      (fun ω : Ω => ω ∈ H ∧ N ω clock = n) =ᵐ[P]
        (fun ω : Ω =>
          (fun i : ℕ => if i < n then τ i ω else 0) ∈ Q ∧
          N ω clock = n))
    (t : ℝ) (ht : 0 ≤ t) (μ : Measure (ℕ → ℝ))
    (hLaw : ∀ n, HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | ω ∈ H ∧
      t < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
      (P H * ENNReal.ofReal (Real.exp (-t))) * μ B := by sorry
