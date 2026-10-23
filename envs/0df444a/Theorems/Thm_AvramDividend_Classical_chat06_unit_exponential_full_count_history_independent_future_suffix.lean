-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_full_count_history_independent_future_suffix
-- name    : AvramDividend.Classical.chat06_unit_exponential_full_count_history_independent_future_suffix
-- status  : Open
-- author  : @WillR
-- created : 2026-10-22T08:15:03.877998+00:00
-- url     : https://prove2.me/theorems/c6d99d68-b70a-4d7b-82a6-305ba86d37ab
-- title:
--   Unit-exponential renewal full count history and future suffix factorisation
-- statement:
--   For an IID sequence of unit-rate exponential waiting times and a renewal count defined by exact arrival thresholds, every event measurable in the entire observed counting history up to a deterministic clock factorises jointly from residual waiting-time survival and any measurable event of the complete infinite future waiting-time suffix. The finite-prefix representation and observed-history measurability are derived from previously proved exact theorems.
-- source:
--   bv_unit_exponential_full_count_history_independent_future_suffix_chat06_20261022.lean, 57 lines, 2797 bytes, SHA-256 72f75c2c4e7d4a461cc56babbacaae54497a3be59834a3a93fb32b8ff01457f1; private probe 3578e20f-23db-4730-845c-c3186d05fd5f reached sentinel without source errors.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_natural_history_count_cylinder_prefix_representation
import Theorems.Thm_AvramDividend_Classical_chat06_observed_count_history_measurable_from_arrival_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_iid_past_residual_full_future_from_threshold

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_unit_exponential_full_count_history_independent_future_suffix
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
    (t : ℝ) (ht : 0 ≤ t)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    P {ω | ω ∈ H ∧
      t < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
      (P H * ENNReal.ofReal (Real.exp (-t))) *
        infinitePi (fun _ : ℕ => expMeasure 1) B := by sorry
