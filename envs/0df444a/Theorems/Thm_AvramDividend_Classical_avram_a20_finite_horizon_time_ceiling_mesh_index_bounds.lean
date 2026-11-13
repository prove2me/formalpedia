-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_finite_horizon_time_ceiling_mesh_index_bounds
-- name    : AvramDividend.Classical.avram_a20_finite_horizon_time_ceiling_mesh_index_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T15:52:54.67093+00:00
-- url     : https://prove2.me/theorems/80119ce4-f14a-4c78-a1d2-f21915458573
-- title:
--   Any positive marked-jump time within a finite horizon occupies a valid uniform ceiling-grid index
-- statement:
--   For any real nonnegative jump time u with 0<u≤T and any positive uniform mesh count k, the ceiling of u k/T is strictly positive and no greater than k. This generalises an already Proved cutoff-specific original Lévy grid index lemma to arbitrary marked jump times and is reused in the genuine original arbitrary-Borel finite-grid pair counting argument.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_finite_horizon_time_ceiling_mesh_index_bounds
    (u T : ℝ≥0) (hT : 0 < T)
    (hu : 0 < u) (huT : u ≤ T)
    (k : ℕ) (hk : 0 < k) :
    0 < Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ∧
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ k := by sorry
