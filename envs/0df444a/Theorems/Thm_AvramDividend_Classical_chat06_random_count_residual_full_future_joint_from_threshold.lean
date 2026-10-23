-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_random_count_residual_full_future_joint_from_threshold
-- name    : AvramDividend.Classical.chat06_random_count_residual_full_future_joint_from_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:38:39.27026+00:00
-- url     : https://prove2.me/theorems/bcd5efb8-b415-4df9-8165-7c82adbc6e32
-- title:
--   Random renewal-count exponential residual and complete future-suffix joint law from arrival thresholds
-- statement:
--   For IID exponential renewal waits, the residual waiting time at any nonnegative deterministic observation clock and the complete sequence of waits after the next claim have a factorised joint survival law. The renewal count is defined pathwise through its exact arrival-threshold equivalence. The previously proved exact count-cylinder theorem establishes the count-event identity needed by the already proved random-count joint law, eliminating that assumption from the final statement. This does not yet claim independence from the entire natural filtration.
-- source:
--   bv_random_count_residual_future_joint_from_threshold_v2_chat06_20261022.lean, 50 lines, 2176 bytes, SHA-256 91a5460d0dc11aa57d08f4ee7650034365fa84e68619cb93d8107d45feb7b669; private remote probe 9e1a9303-4449-479b-be4c-909013e641eb passed sentinel with zero candidate source errors.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_iid_random_count_residual_full_future_joint

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_random_count_residual_full_future_joint_from_threshold
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (hN : Measurable (fun ω => N ω clock))
    (t : ℝ) (ht : 0 ≤ t)
    (μ : Measure (ℕ → ℝ))
    (hLaw : ∀ n,
      HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | t < τ (N ω clock) ω -
      (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
        ENNReal.ofReal (Real.exp (-t)) * μ B := by sorry
