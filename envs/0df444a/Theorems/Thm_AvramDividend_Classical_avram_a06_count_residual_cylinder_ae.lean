-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_count_residual_cylinder_ae
-- name    : AvramDividend.Classical.avram_a06_count_residual_cylinder_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:07:19.925901+00:00
-- url     : https://prove2.me/theorems/4d462b92-93b5-4bf5-bb6e-5b3ff3f36e04
-- title:
--   Almost-sure renewal count residual event is the prefix-sum cylinder
-- statement:
--   If the renewal count threshold identity holds on a common full-measure event, then a fixed-count residual survival event intersected with any sample event coincides almost surely with the finite prefix-sum inequality cylinder. This is the elementary a.e transfer required in the source-model fixed-count residual future independence theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a06_count_residual_cylinder_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (n : ℕ) (Q : Set Ω) (t : ℝ) (ht : 0 ≤ t) :
    {ω | ω ∈ Q ∧ N ω clock = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)} =ᵐ[P]
    {ω | ω ∈ Q ∧ (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
      clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω} := by sorry
