-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB208_martingale_FV_uniform_band_occupation_bound
-- name    : AvramDividend.Classical.avram_gbB208_martingale_FV_uniform_band_occupation_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T00:30:34.42068+00:00
-- url     : https://prove2.me/theorems/b302c308-8ec4-4e6a-b9e5-c7693a62a219
-- title:
--   Uniform pathwise linear small-ball occupation rate for a continuous nondegenerate martingale perturbed by finite variation
-- statement:
--   For a continuous square-integrable martingale with deterministic positive linear quadratic bracket and any sample path of locally bounded variation, the Lebesgue time occupied by a spatial band of radius 1/(k+1) around a fixed level is almost surely at most a random finite constant times that radius, uniformly over k on any finite stopped horizon.
-- source:
--   Core quantitative local-time occupation step. Intended as the single genuinely stochastic child of gbB200; B140+B170 give B200 directly from this rate. No Brownian substitution or adaptedness assumptions for dividend finite variation.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB208_martingale_FV_uniform_band_occupation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (Xsrc : ℝ≥0 → Ω → ℝ) (c σ : ℝ) (hσ : 0 < σ)
    (hM : Martingale (fun t ω =>
      Xsrc t ω - (t : ℝ) * c) 𝓕 P)
    (hQ : Martingale (fun t ω =>
      (Xsrc t ω - (t : ℝ) * c) ^ 2 -
      (t : ℝ) * σ ^ 2) 𝓕 P)
    (hContinuous : ∀ᵐ ω ∂P,
      Continuous (fun t : ℝ≥0 => Xsrc t ω))
    (Dsrc : ℝ≥0 → Ω → ℝ)
    (hFV : ∀ ω, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => Dsrc t ω) Set.univ)
    (x b : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ L : ℝ≥0, ∀ k : ℕ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + Xsrc (Real.toNNReal t) ω -
          Dsrc (Real.toNNReal t) ω - b) <
          (1 : ℝ) / ((k : ℝ) + 1)} ≤
      ENNReal.ofReal ((L : ℝ) / ((k : ℝ) + 1)) := by sorry
