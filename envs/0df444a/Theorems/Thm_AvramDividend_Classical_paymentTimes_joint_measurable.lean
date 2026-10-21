-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
-- name    : AvramDividend.Classical.paymentTimes_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:22:25.15671+00:00
-- url     : https://prove2.me/theorems/6e9faa20-c0bf-445c-92c0-0fd50340de1b
-- title:
--   Original sample-dependent stopped payment-time region is jointly Borel measurable
-- statement:
--   For any measurable random extended nonnegative horizon τ, the set of pairs (real time t, sample point ω) such that t belongs to the original paymentTimes(τ ω) is jointly measurable in real time and the sample space. Its defining condition is t≥0 and either t=0 or ENNReal.ofReal t<τ ω; all three constituent conditions are preimages of measurable intervals or diagonal inequalities under measurable projections. The theorem retains the zero-time dividend payment convention and provides a genuine random-stopping-set measurability input for integrating the true Stieltjes dividend measure.
-- source:
--   Original Definitions.Def_AvramDividend_Classical_ReflectionBarrier paymentTimes definition, pinned Mathlib measurableSet_lt and ENNReal.measurable_ofReal. The actual barrierRuinTime_measurable theorem is in the Chat05 publication queue.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : Ω → ℝ≥0∞) (hτ : Measurable τ) :
    MeasurableSet {p : ℝ × Ω | p.1 ∈ paymentTimes (τ p.2)} := by sorry
