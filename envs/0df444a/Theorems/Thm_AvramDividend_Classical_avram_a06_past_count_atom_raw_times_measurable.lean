-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_past_count_atom_raw_times_measurable
-- name    : AvramDividend.Classical.avram_a06_past_count_atom_raw_times_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:26:40.129334+00:00
-- url     : https://prove2.me/theorems/78eba680-1834-4003-9a27-20c4ba3e2090
-- title:
--   Finite past count-increment atoms at bounded real endpoints are history measurable
-- statement:
--   Finite count-increment predicates indexed by endpoints earlier than the clock are measurable in the full count-history sigma algebra. Indices outside the selected prefix may have arbitrary endpoints, because their implication antecedent is false; clamp those to the clock in the subtype-based cylinder theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_past_count_atom_history_comap_measurable
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a06_past_count_atom_raw_times_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (N : Ω → ℝ → ℕ) (clock : ℝ)
    (n : ℕ) (a b : Fin n → ℝ) (j : Fin n) (v : Fin n → ℕ)
    (ha : ∀ i : Fin n, i < j → a i ≤ clock)
    (hb : ∀ i : Fin n, i < j → b i ≤ clock) :
    MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))]
      {ω | ∀ i : Fin n, i < j →
        N ω (b i) - N ω (a i) = v i} := by sorry
