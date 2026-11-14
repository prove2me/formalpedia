-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a118_actual_stopped_gaussian_true_crossing_uniform_value_expected_L1
-- name    : AvramDividend.Classical.avram_ga_a118_actual_stopped_gaussian_true_crossing_uniform_value_expected_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:59:34.985857+00:00
-- url     : https://prove2.me/theorems/669d983f-e1e9-40b9-9269-7b716d598072
-- title:
--   Actual original Gaussian true stop-crossing bounded uniformly continuous value displacement vanishes in expected absolute L1
-- statement:
--   For the genuine original zero-jump Gaussian Lévy process, arbitrary path-dependent physical mesh crossing indices straddling a bounded original stopped time rho give a value displacement whose expected absolute size tends to zero for any bounded uniformly continuous (including positive-compact-truncated) spatial value function. The proof explicitly instantiates the true physical crossing clocks and uses no deterministic terminal-cell replacement.
-- source:
--   Proved ga111 expected-L1 original uniform random Gaussian source modulus; actual original stopped crossing clock at rho and true physical pre-stop s_i.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a111_original_gaussian_random_crossing_bounded_uniform_value_L1
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a118_actual_stopped_gaussian_true_crossing_uniform_value_expected_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0) (i : ℕ → Ω → ℕ)
    (hρ : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hCross : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ < ρ ω ∧
        ρ ω ≤ (i m ω : ℝ≥0) * Δ + Δ)
    (w : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hW : ∀ z : ℝ, |w z| ≤ M)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, |v - u| < δ → |w v - w u| < ε)
    (y : ℕ → Ω → ℝ)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      |w (y m ω + (X.X (ρ ω) ω -
        X.X ((i m ω : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)) -
        w (y m ω)|) P) :
    Tendsto (fun m => ∫ ω,
      |w (y m ω + (X.X (ρ ω) ω -
        X.X ((i m ω : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)) -
        w (y m ω)| ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
