-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a38_original_true_stop_crossing_uniform_grid_clock_gap
-- name    : AvramDividend.Classical.avram_a38_original_true_stop_crossing_uniform_grid_clock_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:29:07.818362+00:00
-- url     : https://prove2.me/theorems/c9e21e78-ff5e-4bc2-b868-aac7dc54a942
-- title:
--   Original actual stopped Gaussian canonical unique crossing clock belongs to bounded horizon with mesh gap
-- statement:
--   For an original physical stopped clock ρ≤n and its actual unique canonical uniform-mesh crossing cell indexed i_m, where s_m=i_mΔ_m≤ρ≤s_m+Δ_m, show both original time coordinates s_m and ρ belong to [0,n], and their NNReal distance is at most Δ_m=n/(m+1). This is the exact time-gap hypothesis for existing Proved true-original-X random Gaussian crossing increment and discounted full-band L1 lemmas; no stochastic martingale or source budget invented.
-- source:
--   Original finitecap stopped physical Gaussian uniform crossing grid actual random clock s_m and ρ, used to instantiate a35/a36 true random time increment source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_a38_original_true_stop_crossing_uniform_grid_clock_gap
    {Ω : Type*} (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρ : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (i : ℕ → Ω → ℕ)
    (hCell : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ ≤ ρ ω ∧
        ρ ω ≤ (i m ω : ℝ≥0) * Δ + Δ) :
    ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      s ∈ Set.Icc 0 (n : ℝ≥0) ∧
        ρ ω ∈ Set.Icc 0 (n : ℝ≥0) ∧
        dist s (ρ ω) ≤ (Δ : ℝ) := by sorry
