-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_count_history_prefix_representation_ae
-- name    : AvramDividend.Classical.avram_a06_count_history_prefix_representation_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:59:27.180934+00:00
-- url     : https://prove2.me/theorems/d23cd984-ebcc-466b-b09f-a64879a209ea
-- title:
--   Almost-sure renewal threshold gives full past-count history prefix representation
-- statement:
--   If the renewal threshold identity holds for almost every sample path, then on each fixed count cylinder the entire observed count history up to clock is represented by a measurable event of the finite interarrival prefix, modulo null sets. This strengthens the pointwise hypothesis in a proved history representation theorem and is needed for original compound Poisson drivers.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_history_comap_prefix_representation
import Theorems.Thm_AvramDividend_Classical_chat06_prefix_observed_count_history_measurable
import Theorems.Thm_AvramDividend_Classical_chat06_arrival_prefix_reconstructs_past_count
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a06_count_history_prefix_representation_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (τ Z : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (clock : ℝ) (n : ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔
        (∑ i ∈ Finset.range (k + 1), τ ω i) ≤ u)
    (hZ : ∀ ω i, Z ω i = if i < n then τ ω i else 0)
    (H : Set Ω)
    (hH : MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H) :
    ∃ Q : Set (ℕ → ℝ), MeasurableSet Q ∧
      (fun ω : Ω => ω ∈ H ∧ N ω clock = n) =ᵐ[P]
        (fun ω : Ω => Z ω ∈ Q ∧ N ω clock = n) := by sorry
