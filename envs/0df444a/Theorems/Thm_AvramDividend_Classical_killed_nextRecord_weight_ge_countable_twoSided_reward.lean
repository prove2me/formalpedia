-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_nextRecord_weight_ge_countable_twoSided_reward
-- name    : AvramDividend.Classical.killed_nextRecord_weight_ge_countable_twoSided_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:25:25.480472+00:00
-- url     : https://prove2.me/theorems/360e325c-f895-4d89-810e-a7d7057feb80
-- title:
--   The next killed record dominates the countable measurable shifted two-sided exit reward
-- statement:
--   For a realised surviving record b at a finite time u, its discounted next-record payment dominates the prior discount times the explicitly countable future two-sided exit reward. This combines the proved actual killed-record pathwise domination with the proved shifted Lévy schedule identity, placing the payoff directly in the measurable form required by the stopped strong-Markov step.
-- source:
--   Composition of the Proved killed_nextRecord_weight_ge_shifted_twoSided_reward and levy_shifted_trueTwoSided_reward_eq_schedule.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_weight_ge_shifted_twoSided_reward
import Theorems.Thm_AvramDividend_Classical_levy_shifted_trueTwoSided_reward_eq_schedule

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_nextRecord_weight_ge_countable_twoSided_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω) :
    ENNReal.ofReal ε *
      (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        (let g : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
         let τ : ℕ → ℝ≥0 := fun j =>
           ((Nat.unpair j).2 : ℝ≥0) *
             (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
         let ρ : ℝ≥0∞ := ⨅ j : ℕ,
           if ε < g (τ j) then (τ j : ℝ≥0∞) else ⊤
         let σ : ℝ≥0∞ := ⨅ j : ℕ,
           if g (τ j) < ε - a then (τ j : ℝ≥0∞) else ⊤
         if ρ < σ then
           ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
         else 0)) ≤
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
     else 0) := by sorry
