-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_countwise_iid_past_residual_full_suffix_from_threshold
-- name    : AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_from_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:19:51.011932+00:00
-- url     : https://prove2.me/theorems/7c0d1e71-7759-479c-a107-f279e5744fd9
-- title:
--   Countwise measurable past representation yields residual and complete future-suffix joint factorisation
-- statement:
--   For an IID interarrival family satisfying a renewal arrival-threshold identity, any measurable past event H whose restriction to each exact-count cylinder is measurably representable by the first n waiting times factorises jointly from survival of the selected residual exponential waiting time and any measurable event of the complete selected future waiting-time suffix. The proof invokes the now accepted fixed-count prefix-event residual/full-suffix product law and glues across all count cylinders using the accepted countwise representation theorem. It replaces the abstract factorisation hypothesis of the earlier gluing helper by explicit IID and exponential-tail assumptions.
-- source:
--   bv_countwise_iid_past_residual_full_suffix_from_threshold_v2_chat06_20261022.lean, 71 lines, 3225 bytes, SHA-256 df958a2a2f1e7f675888db65de014bceedece814e715165a9df3ef13835e1088; private probe 52bab34e-d04c-4da0-b343-e322bf42398b reached sentinel with zero candidate errors. V1 failed line 68 due to typo hG vs hGm, preserved.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_countwise_prefix_representation_implies_past_independence
import Theorems.Thm_AvramDividend_Classical_chat06_iid_fixed_count_prefix_event_residual_future_joint_from_threshold

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_from_threshold
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (hN : Measurable (fun ω => N ω clock))
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
