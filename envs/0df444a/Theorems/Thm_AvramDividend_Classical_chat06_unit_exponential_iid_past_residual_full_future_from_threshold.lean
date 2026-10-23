-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_iid_past_residual_full_future_from_threshold
-- name    : AvramDividend.Classical.chat06_unit_exponential_iid_past_residual_full_future_from_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T08:05:09.91812+00:00
-- url     : https://prove2.me/theorems/620a5092-8440-4734-b298-bca24da8fdba
-- title:
--   Unit-exponential IID renewal residual and full future suffix factorisation
-- statement:
--   For IID unit-rate exponential interarrival variables, the arrival-threshold count relation and countwise prefix representation of an observed-past event imply the exact joint factorisation between that event, residual waiting-time survival at t and every measurable event of the entire future waiting-time suffix. The proof derives count measurability, the product-law distribution of every shifted suffix and exponential survival directly from accepted helper theorems. No separate tail-law, suffix-law or count-measurability assumption is needed.
-- source:
--   bv_unit_exponential_iid_past_residual_full_future_from_threshold_chat06_20261022.lean, 46 lines, 2145 bytes, SHA-256 041d3b02c39be73ad6754cb5245d6ef2ba8dfbc562795f95d3d92f712397e665; private probe 286e9efc-f4d6-4020-b80d-12e4dc0af936 reached sentinel without candidate errors.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_countwise_iid_past_residual_full_suffix_common_law
import Theorems.Thm_AvramDividend_Classical_chat06_count_measurable_from_arrival_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_haslaw_survival

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_unit_exponential_iid_past_residual_full_future_from_threshold
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (hExp : ∀ i, HasLaw (τ i) (expMeasure 1) P)
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
    (t : ℝ) (ht : 0 ≤ t)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    P {ω | ω ∈ H ∧
      t < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
      (P H * ENNReal.ofReal (Real.exp (-t))) *
        infinitePi (fun _ : ℕ => expMeasure 1) B := by sorry
