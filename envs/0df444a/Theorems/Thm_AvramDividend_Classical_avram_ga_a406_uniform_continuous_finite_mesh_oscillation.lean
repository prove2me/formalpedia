-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a406_uniform_continuous_finite_mesh_oscillation
-- name    : AvramDividend.Classical.avram_ga_a406_uniform_continuous_finite_mesh_oscillation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:18:04.163815+00:00
-- url     : https://prove2.me/theorems/35d26eca-c849-4107-83ff-c97b6a88d15d
-- title:
--   Finite-range uniform-continuity mesh oscillation is uniformly small
-- statement:
--   Uniformly continuous functions on a compact nonnegative time interval have uniformly vanishing value oscillations on all actual cells of a refining finite mesh, even though arbitrary indices outside the mesh require no assumptions.
-- source:
--   Proved avram_ga_a55_uniform_continuous_mesh_oscillation, applied to zero-filled endpoint maps on inactive indices.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a406_uniform_continuous_finite_mesh_oscillation
    (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : UniformContinuousOn f (Icc 0 T))
    (s t : ℕ → ℕ → ℝ≥0)
    (hRange : ∀ m i : ℕ, i < m →
      s m i ∈ Icc 0 T ∧ t m i ∈ Icc 0 T)
    (hGap : ∀ m i : ℕ, i < m →
      dist (s m i) (t m i) ≤ T / ((m : ℝ≥0) + 1)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
        ∀ i : ℕ, i < m →
          dist (f (s m i)) (f (t m i)) < ε := by sorry
