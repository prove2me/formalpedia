-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_zero_future_factor_from_ae_history
-- name    : AvramDividend.Classical.avram_a06_zero_future_factor_from_ae_history
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:36:34.925351+00:00
-- url     : https://prove2.me/theorems/5183ae98-2f81-477c-b788-03fb0e8766e1
-- title:
--   Zero future renewal increment factors from the observed past under almost-sure threshold
-- statement:
--   Under iid unit-exponential interarrivals and an a.e renewal threshold identity, an event of the observed counting history up to clock is independent of the event of zero future renewals over the next nonnegative time interval. Additional measurable count and past-event hypotheses are stated explicitly for applicability to the original compound Poisson source.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_count_history_prefix_representation_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_increment_zero_atom_suffix_cylinder_ae
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_haslaw_survival
open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_zero_future_factor_from_ae_history
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
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | ω ∈ H ∧ N ω (clock + t) - N ω clock = 0} =
      P H * ENNReal.ofReal (Real.exp (-t)) := by sorry
