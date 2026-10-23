-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_natural_history_count_cylinder_prefix_representation
-- name    : AvramDividend.Classical.chat06_natural_history_count_cylinder_prefix_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:44:33.84251+00:00
-- url     : https://prove2.me/theorems/11e02130-9f70-40dc-97d1-77458232b903
-- title:
--   Complete count history is determined by finite arrival prefixes on fixed-count cylinders
-- statement:
--   The complete renewal counting history up to a deterministic observation horizon is a measurable function of the first n interarrival times whenever the renewal count at the horizon is n. The explicit prefix-to-history map counts finite arrivals at every prior time. Pathwise count reconstruction and the accepted comap-sigma-algebra representation lemma show that every natural-history event H agrees, on the count-n cylinder, almost surely with a measurable event Q of the finite prefix. This discharges the remaining observed-history representation hypothesis needed for residual waiting-time and future-IID independence.
-- source:
--   bv_natural_history_count_cylinder_prefix_representation_v2_chat06_20261022.lean, 48 lines, 2236 bytes, SHA-256 c13f09379af1dab703fe9cd8cd1ad9f75e7e8c20a382c423b873a8b429496ac5. Probe bfd7c16e-ca53-4f0a-9d22-a15186ab96fc reached intentional sentinel with zero source errors.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Theorems.Thm_AvramDividend_Classical_chat06_history_comap_prefix_representation
import Theorems.Thm_AvramDividend_Classical_chat06_prefix_observed_count_history_measurable
import Theorems.Thm_AvramDividend_Classical_chat06_arrival_prefix_reconstructs_past_count

open MeasureTheory Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_natural_history_count_cylinder_prefix_representation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (τ Z : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (clock : ℝ) (n : ℕ)
    (hThreshold : ∀ ω u k,
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
