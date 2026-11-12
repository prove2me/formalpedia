-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_countwise_iid_residual_future_joint_ae
-- name    : AvramDividend.Classical.avram_a06_countwise_iid_residual_future_joint_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:36:27.265488+00:00
-- url     : https://prove2.me/theorems/2d28a726-424e-4c77-a8cf-912999d4a3e8
-- title:
--   IID exponential renewal past-event residual and future suffix factorisation under a.e threshold
-- statement:
--   Countwise measurable past-history representations imply independence of residual exponential survival and a measurable event of the entire future iid suffix, assuming only the almost-sure renewal count threshold. The existing pointwise-threshold result is proved; this version uses the new a.e fixed-count cylinder factorisation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_countwise_prefix_representation_implies_past_independence
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_countwise_iid_residual_future_joint_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
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
