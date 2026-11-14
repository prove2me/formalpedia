-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a66_true_stopped_gaussian_taylor_positive_L1_from_raw_energy
-- name    : AvramDividend.Classical.avram_ga_a66_true_stopped_gaussian_taylor_positive_L1_from_raw_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:38:18.67702+00:00
-- url     : https://prove2.me/theorems/1f38721e-29c6-4dfe-87d4-efa40bac5358
-- title:
--   True physical stopped Gaussian positive Taylor L1 tends zero from C2 compact modulus, raw quadratic energy and source tail decay
-- statement:
--   For true stop-masked physical Gaussian mesh coefficients with nonnegative compact C2 Taylor remainder and arbitrarily small coefficients on short raw increments, a uniform stopped quadratic source energy budget and vanishing expected rare raw increments imply expected positive Taylor error convergence to zero.
-- source:
--   Direct main b0d9951c positive-only safe stopped original source Gaussian spatial Taylor expectation bridge using ga_a58 and ga_a59.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a66_true_stopped_gaussian_taylor_positive_L1_from_raw_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : ℕ → ℕ → ℝ≥0) (ρ : Ω → ℝ≥0)
    (a z : ℕ → ℕ → Ω → ℝ)
    (δ : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hAInt : ∀ m, Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s m i < ρ ω then
        a m i ω * (z m i ω)^2 else 0) P)
    (hEInt : ∀ m, Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s m i < ρ ω then
        (z m i ω)^2 else 0) P)
    (hTInt : ∀ j m, Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s m i < ρ ω then
        (if δ j ≤ |z m i ω| then (z m i ω)^2 else 0) else 0) P)
    (hEbound : ∀ m, (∫ ω, (∑ i ∈ Finset.range m,
        if s m i < ρ ω then (z m i ω)^2 else 0) ∂P) ≤ K)
    (hCoeff : ∀ ε : ℝ, 0 < ε →
      ∃ (j : ℕ) (M : ℝ),
        0 ≤ M ∧
        (∀ m ω i, i ∈ Finset.range m → s m i < ρ ω → 0 ≤ a m i ω) ∧
        (∀ m ω i, i ∈ Finset.range m → s m i < ρ ω → a m i ω ≤ M) ∧
        (∀ m ω i, i ∈ Finset.range m → s m i < ρ ω →
          |z m i ω| < δ j → a m i ω ≤ ε))
    (hTtail : ∀ j, Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m,
        if s m i < ρ ω then
          (if δ j ≤ |z m i ω| then (z m i ω)^2 else 0)
        else 0) ∂P) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m : ℕ => ∫ ω, (∑ i ∈ Finset.range m,
      if s m i < ρ ω then a m i ω * (z m i ω)^2
      else 0) ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
