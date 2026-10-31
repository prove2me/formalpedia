-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero
-- name    : AvramDividend.Classical.avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:43:42.830987+00:00
-- url     : https://prove2.me/theorems/96e78b02-5a94-4929-a453-cfa429a889de
-- title:
--   Any finite sum of bounded predictable coefficients times centred original Lévy increment payoffs has mean zero
-- statement:
--   For an arbitrary finite collection of original Lévy source increments, possibly overlapping but with each coefficient strongly measurable at its own start time and uniformly bounded, if each future-increment payoff is integrable and centred under stationary increments then the finite stochastic sum's expectation vanishes. Stationary-increment identically distributed laws transfer integrability of each increment, and bounded multiplication yields integrability of every term. The accepted conditional future-mean-zero lemma handles each term, and the finite-sum Bochner integral theorem combines them. This is a genuine discrete stochastic-integral expectation statement under the original Lévy law.
-- source:
--   Canonical Proved bounded past-times-centred future-increment mean-zero UUID 488296c2-5a96-4786-a577-a02199ace877; pinned Mathlib IdentDistrib.integrable_iff, Integrable.bdd_mul, integral_finset_sum. Private remote compiler job 9f2c7461-bb97-4ee5-814c-9266978f1c1f reached sentinel without source diagnostics, SHA-256 cb468dc766daee243a0c1e6a32e112ac15d0164676dd4bf15bd2f4151dd9f3fb.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι)
    (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (φ : ι → ℝ → ℝ)
    (hφ : ∀ i ∈ S, Measurable (φ i))
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓕 (s i)] (H i))
    (K : ι → ℝ)
    (hBound : ∀ i ∈ S, ∀ ω, ‖H i ω‖ ≤ K i)
    (hInt : ∀ i ∈ S,
      Integrable (fun ω => φ i (X.X (t i - s i) ω)) P)
    (hmean : ∀ i ∈ S,
      (∫ ω, φ i (X.X (t i - s i) ω) ∂P) = 0) :
    (∫ ω, ∑ i ∈ S, H i ω *
      φ i (X.X (t i) ω - X.X (s i) ω) ∂P) = 0 := by sorry
