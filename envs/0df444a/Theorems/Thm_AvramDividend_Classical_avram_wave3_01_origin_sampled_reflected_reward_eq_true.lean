-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_origin_sampled_reflected_reward_eq_true
-- name    : AvramDividend.Classical.avram_wave3_01_origin_sampled_reflected_reward_eq_true
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:15:18.319361+00:00
-- url     : https://prove2.me/theorems/5eaa3147-152e-4b98-ac27-3c8669069ca9
-- title:
--   Actual Lévy origin reflected-killed record reward equals its countable Borel-clock evaluation
-- statement:
--   For every path of the genuine spectrally negative Lévy process, the Cantor-grid Borel upper-record and reflected drawdown clocks at the original origin yield exactly the genuine strict first-upcrossing-before-reflected-ruin discounted reward. The nontrivial source path equality uses the Proved pair of shifted true clocks and the source pathwise zero-origin condition. It is the exact bridge between the accepted stopped strong-Markov measurable future reward and the source uncapped discounted reflected record expectation.
-- source:
--   avram_wave3_01_true_shifted_record_ruin_clock_pair (acce5dd9); source original first upcrossing and reflected ruin definitions; prerequisite for uncapped semigroup 3890ee9b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_origin_sampled_reflected_reward_eq_true
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a c q : ℝ) (ω : Ω) :
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let f : ℝ≥0 → ℝ := fun t => X.X t ω
     let ρ : ℝ≥0∞ := ⨅ i : ℕ,
       if c < f (samples i) - f 0 then (samples i : ℝ≥0∞) else ⊤
     let σ : ℝ≥0∞ := ⨅ i : ℕ,
       if f (samples i) - f 0 -
         (⨆ j : ℕ, if samples j ≤ samples i
           then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal < -a
         then (samples i : ℝ≥0∞) else ⊤
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) =
    (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
       ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
     else 0) := by sorry
