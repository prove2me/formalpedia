-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_zero_future_count_atom_factor_from_full_history
-- name    : AvramDividend.Classical.avram_a06_zero_future_count_atom_factor_from_full_history
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:08:09.661925+00:00
-- url     : https://prove2.me/theorems/fcdf113e-5158-4d7e-afd2-84a53b436152
-- title:
--   Zero original renewal-count increments factor against every observed count-history event
-- statement:
--   For an IID unit-exponential renewal process whose count satisfies its exact arrival threshold, the zero future increment event is independent of all measurable observed count-history events at the clock. This is the zero-count atom of the original-process finite-dimensional independent-increments proof.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_full_count_history_independent_future_suffix
import Theorems.Thm_AvramDividend_Classical_avram_a06_increment_zero_atom_suffix_cylinder_ae
open MeasureTheory Measure ProbabilityTheory Set Finset
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_zero_future_count_atom_factor_from_full_history
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (hExp : ∀ i, HasLaw (τ i) (expMeasure 1) P)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (H : Set Ω)
    (hHpast : MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | ω ∈ H ∧ N ω (clock + t) - N ω clock = 0} =
      P H * ENNReal.ofReal (Real.exp (-t)) := by sorry
