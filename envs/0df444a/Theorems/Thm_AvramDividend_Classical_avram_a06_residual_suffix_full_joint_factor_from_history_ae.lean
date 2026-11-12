-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_residual_suffix_full_joint_factor_from_history_ae
-- name    : AvramDividend.Classical.avram_a06_residual_suffix_full_joint_factor_from_history_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:37:02.269571+00:00
-- url     : https://prove2.me/theorems/60167e90-6732-4e50-b52e-5dc786c31474
-- title:
--   Full residual waiting time and post-arrival suffix independent of the observed renewal count history under an a.e. threshold
-- statement:
--   For IID unit-exponential interarrival times and the almost-sure renewal-count threshold, the joint pair consisting of the remaining wait at a deterministic clock and the complete future waiting-time sequence is independent of every measurable observed past-count-history event. Prove via the established countwise a.e. residual/suffix tail-by-cylinder factorisation followed by Borel product-measure uniqueness. This is the substantive measure-theoretic child needed for every positive future count atom.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_count_history_prefix_representation_ae
open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_residual_suffix_full_joint_factor_from_history_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (hExp : ∀ i, HasLaw (τ i) (expMeasure 1) P)
    (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (hN : Measurable (fun ω => N ω clock))
    (H : Set Ω) (hH : MeasurableSet H)
    (hHpast : MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H)
    (D : Set (ℝ × (ℕ → ℝ))) (hD : MeasurableSet D) :
    P {ω | ω ∈ H ∧
      (τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω),
        (fun j : ℕ => τ (N ω clock + 1 + j) ω)) ∈ D} =
      P H * P {ω |
        (τ (N ω clock) ω -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω),
          (fun j : ℕ => τ (N ω clock + 1 + j) ω)) ∈ D} := by sorry
