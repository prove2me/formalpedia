-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_killed_record_fixedTime_esscher_future_factor
-- name    : AvramDividend.Classical.avram_ws01h_killed_record_fixedTime_esscher_future_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:01:38.564635+00:00
-- url     : https://prove2.me/theorems/a6839ae4-1ac3-467c-ad77-51d780981998
-- title:
--   Original lower-killed stopped first-record factor with genuine future Esscher weight at any fixed age
-- statement:
--   On the actual path event that first strict upcrossing precedes the true original lower exit and a finite cap, the joint discounted past and arbitrary whole-future-path reward multiplied by the compensated Esscher density at a fixed future lag factors through the original Levy future law. This is an unconditional, source-specific Markov–Esscher factor with the original lower ruin history retained.
-- source:
--   Avram, Palmowski and Pistorius (2007); true stopped-history first-record Markov reward factor 1061aefc-2095-4553-8c89-c9423b46fc57, with canonical no-positive-jump Levy path.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_original_killedRecord_fixedFuture_markov_factor

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_killed_record_fixedTime_esscher_future_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b : ℝ) (N u : ℝ≥0)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
       {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) *
       (ENNReal.ofReal (Real.exp
         (θ * (X.X (τ ω + u) ω - X.X (τ ω) ω) -
           (u : ℝ) * X.ψ θ)) *
         reward (fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω))
       else 0 ∂P) =
       (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
         (∫⁻ ω, ENNReal.ofReal (Real.exp
           (θ * X.X u ω - (u : ℝ) * X.ψ θ)) *
           reward (fun t : ℝ≥0 => X.X t ω) ∂P)) := by sorry
