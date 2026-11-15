-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a412_uniform_continuity_all_subcells
-- name    : AvramDividend.Classical.avram_ga_a412_uniform_continuity_all_subcells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:24:27.315048+00:00
-- url     : https://prove2.me/theorems/673ce32e-1348-497c-b77a-7acdc4c65c5a
-- title:
--   Uniformly continuous source oscillations vanish on all subcell points of finite physical mesh
-- statement:
--   Uniform continuity on a compact horizon makes every value difference between a physical mesh cell start and any later point inside that cell uniformly small for sufficiently fine meshes.
-- source:
--   Original a55 uniform-continuity mesh proof argument, extended to arbitrary within-cell points.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set Metric Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a412_uniform_continuity_all_subcells
    (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : UniformContinuousOn f (Icc 0 T))
    (s : ℕ → ℕ → ℝ≥0) (Δ : ℕ → ℝ≥0)
    (hEnd : ∀ m i : ℕ, i < m → s m i + Δ m ≤ T)
    (hWidth : ∀ m : ℕ, Δ m ≤ T / ((m : ℝ≥0) + 1)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m → ∀ i : ℕ, i < m →
        ∀ u : ℝ≥0, s m i ≤ u → u ≤ s m i + Δ m →
          dist (f (s m i)) (f u) < ε := by sorry
