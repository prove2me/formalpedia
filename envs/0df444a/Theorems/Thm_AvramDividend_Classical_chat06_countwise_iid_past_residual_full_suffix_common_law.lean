-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_countwise_iid_past_residual_full_suffix_common_law
-- name    : AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_common_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:35:52.494729+00:00
-- url     : https://prove2.me/theorems/0c8745a5-a345-4f5c-82d4-43c02815673c
-- title:
--   Countwise past residual-future joint law with canonical IID infinite-product suffix
-- statement:
--   For measurable IID interarrival variables sharing law ν, the entire shifted future suffix has the infinite product law infinitePi ν. Combining the accepted common-suffix-law theorem with the accepted countwise past-event gluing theorem yields factorisation of arbitrary measurable past H, residual waiting-time survival, and every measurable event B of the infinite future suffix, assuming a countwise finite-prefix representation of H. This eliminates a separately assumed common suffix-law hypothesis from the gluing result.
-- source:
--   bv_countwise_iid_past_residual_full_suffix_common_law_chat06_20261022.lean, 47 lines, 2160 bytes, SHA-256 6bc647fb29a5df1a7949a6ad2d46c213d0caa1bc3560786115a762fb6df1b062; remote private probe 8c144634-b0ed-448c-ae37-4b344a0057dd reached sentinel without candidate errors.

import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_countwise_iid_past_residual_full_suffix_from_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_iid_shifted_suffix_common_infinite_product_law

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_common_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (ν : Measure ℝ) (hν : ∀ i, HasLaw (τ i) ν P)
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
    (t : ℝ) (ht : 0 ≤ t)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | ω ∈ H ∧
      t < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
      (P H * ENNReal.ofReal (Real.exp (-t))) *
        infinitePi (fun _ : ℕ => ν) B := by sorry
