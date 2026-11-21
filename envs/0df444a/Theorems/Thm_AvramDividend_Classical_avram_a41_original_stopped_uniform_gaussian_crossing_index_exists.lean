-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a41_original_stopped_uniform_gaussian_crossing_index_exists
-- name    : AvramDividend.Classical.avram_a41_original_stopped_uniform_gaussian_crossing_index_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:40:58.679865+00:00
-- url     : https://prove2.me/theorems/fac4036a-92c7-408c-b9a8-c8e227e22fd3
-- title:
--   Construct actual physical canonical uniform Gaussian crossing cell index for every bounded stopped clock
-- statement:
--   Given positive integer horizon n and a true original bounded stopped random time ρ(ω)∈[0,n], construct deterministically for each mesh m and each original sample ω an integer crossing-cell index i_m(ω) satisfying i_mΔ≤ρ≤(i_m+1)Δ, with exact Δ=n/(m+1) in NNReal. Explicit choice is Nat.floor(ρ/Δ), using finite uniform mesh and Archimedean floor inequalities. This removes the auxiliary existential crossing-index assumption in original actual Gaussian stopped positive L1 source a39/a40 and remains valid at both grid boundaries. Pure original stopping-grid geometry, no invented stochastic process.
-- source:
--   Original bounded Gaussian physical stopped clock uniform mesh selection via Nat.floor, to instantiate fullband original same-X L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a41_original_stopped_uniform_gaussian_crossing_index_exists
    {Ω : Type*} (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0) (hρ : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    ∃ i : ℕ → Ω → ℕ, ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ ≤ ρ ω ∧
        ρ ω ≤ (i m ω : ℝ≥0) * Δ + Δ := by sorry
