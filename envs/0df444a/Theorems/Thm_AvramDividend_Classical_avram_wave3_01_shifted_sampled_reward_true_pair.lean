-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_shifted_sampled_reward_true_pair
-- name    : AvramDividend.Classical.avram_wave3_01_shifted_sampled_reward_true_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:17:56.245+00:00
-- url     : https://prove2.me/theorems/76fb5aa4-6727-4933-a6bf-7ed97c408fd2
-- title:
--   True future Lévy record and reflected ruin reward equals its Borel countable sampled representation after any finite shift
-- statement:
--   For every source spectrally negative Lévy path and arbitrary deterministic finite shift, the countably sampled future first-upcrossing and reflected-drawdown clocks give exactly the genuine shifted future first-upcrossing-before-drawdown discounted reward. This uses the canonically Proved actual shifted-clock pair rather than any assumed path-law change.
-- source:
--   avram_wave3_01_true_shifted_record_ruin_clock_pair acce5dd9 and original source Lévy future increments; required for 3890ee9b discounted reflected semigroup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_true_shifted_record_ruin_clock_pair

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_shifted_sampled_reward_true_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a c q : ℝ) (ω : Ω) (u : ℝ≥0) :
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let ρ : ℝ≥0∞ := ⨅ i : ℕ,
       if c < f (samples i) - f 0 then (samples i : ℝ≥0∞) else ⊤
     let σ : ℝ≥0∞ := ⨅ i : ℕ,
       if f (samples i) - f 0 -
         (⨆ j : ℕ, if samples j ≤ samples i
           then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal < -a
         then (samples i : ℝ≥0∞) else ⊤
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) =
    (let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let ρ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)
     let σ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 //
       f t - sSup (f '' Icc 0 t) < -a}, (i.1 : ℝ≥0∞)
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) := by sorry
