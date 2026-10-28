-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_nextRecord_uncapped_ge_capped_shiftedReward
-- name    : AvramDividend.Classical.killed_nextRecord_uncapped_ge_capped_shiftedReward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:14:50.183991+00:00
-- url     : https://prove2.me/theorems/5a6441fb-86d1-4c9d-9e75-28f8595eae38
-- title:
--   Uncapped next killed record dominates capped first-record shifted exit reward
-- statement:
--   On the event that the first upward record is reached before reflected ruin and before a finite observation cap, the capped first-record clock equals the true clock. At that true first record, spectral negativity forces the path to attain the level, permitting the proved countable two-sided exit lower domination to bound the next uncapped surviving record reward. This supplies the pathwise inequality needed for monotone uncapping of the lower Markov renewal step.
-- source:
--   Proved firstRecord_capped_clock_eq_uncapped_of_le_horizon, firstUpcrossing_attains_peak and killed_nextRecord_weight_ge_countable_twoSided_reward.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_weight_ge_countable_twoSided_reward

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_nextRecord_uncapped_ge_capped_shiftedReward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0) (ω : Ω) :
    (if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
       let u : ℝ≥0 := (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
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
         if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0))
      else 0) ≤
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
     else 0) := by sorry
