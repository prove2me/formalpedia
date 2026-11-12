-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_count_residual_future_joint_ae
-- name    : AvramDividend.Classical.avram_a06_fixed_count_residual_future_joint_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:04:28.150486+00:00
-- url     : https://prove2.me/theorems/277b7b34-d0e5-48e2-9953-87ea92170a83
-- title:
--   Almost-sure renewal threshold implies fixed-count residual and future joint factorisation
-- statement:
--   For iid exponential renewal waiting times and any sample-path count whose renewal threshold identity holds almost surely, the joint factorisation of a measurable finite-prefix event, the residual waiting time and the whole future iid suffix continues to hold. The earlier pointwise version is proved, but the original compound Poisson driver only has the threshold identity almost surely.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_past_residual_full_future_joint_law
import Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_fixed_count_residual_future_joint_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
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
