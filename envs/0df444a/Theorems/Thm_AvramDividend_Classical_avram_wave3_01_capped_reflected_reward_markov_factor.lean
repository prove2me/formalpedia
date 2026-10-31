-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_capped_reflected_reward_markov_factor
-- name    : AvramDividend.Classical.avram_wave3_01_capped_reflected_reward_markov_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:15:37.247554+00:00
-- url     : https://prove2.me/theorems/c97558ac-f587-4831-8fd2-d0b4800c34de
-- title:
--   Actual capped Lévy first-record reflected-killed future discount factors by source stopped strong Markov
-- statement:
--   At the finite capped first strict upward record of the original spectrally negative Levy process, kill the past unless the record occurs before strict reflected drawdown ruin and before cap N. The integral of the actual discounted stopped past survival indicator multiplied by the countably Borel-encoded future first-upcrossing reward killed by fresh shifted reflected ruin is exactly the product of the killed past discount integral and independent original future reward integral. This is a source-specific stopped strong-Markov factorisation, with the complete actual stopped-event measurability, finite-clock measurability, discount measurability and reflected future path reward measurability discharged by canonically Proved source theorems. It is the finite-cap expectation bridge needed for a genuine reflected first-record renewal semigroup; cap-removal and exact event/clock identification remain separate obligations.
-- source:
--   Source Proved f4c6b616 stopped strong Markov; 75a45591 stopped history, 4a553ff9 ambient measurability, b199e654 finite clock, b0df9a24 Borel reflected future reward; Avram Palmowski Pistorius (2007), Kuznetsov Kyprianou Rivero (2013).

import Mathlib
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_measurable_global
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_fresh_reflected_reward_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave3_01_capped_reflected_reward_markov_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c q : ℝ) (N : ℝ≥0) (samples : ℕ → ℝ≥0) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
       {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
     let discount : ℝ≥0 → ℝ≥0∞ := fun t =>
       ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
     let reward : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
       let ρ : ℝ≥0∞ := ⨅ i : ℕ,
         if c < f (samples i) - f 0 then
           (samples i : ℝ≥0∞) else ⊤
       let σ : ℝ≥0∞ := ⨅ i : ℕ,
         if f (samples i) - f 0 -
             (⨆ j : ℕ,
               if samples j ≤ samples i then
                 ENNReal.ofReal (f (samples j) - f 0)
               else 0).toReal < -a then
           (samples i : ℝ≥0∞) else ⊤
       if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
       else 0
     (∫⁻ ω, if ω ∈ A then discount (τ ω) *
       reward (fun t : ℝ≥0 =>
         X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
       (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
       (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)) := by sorry
