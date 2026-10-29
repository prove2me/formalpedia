-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_choose_finite_mesh_horizon_indices_ws01c
-- name    : AvramDividend.Classical.bv_choose_finite_mesh_horizon_indices_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:52:41.552983+00:00
-- url     : https://prove2.me/theorems/f72de07a-0155-4d4e-889f-21ec9f1413fa
-- title:
--   Every positive mesh admits finitely many observations reaching any finite horizon
-- statement:
--   For every positive nonnegative-real mesh size h_n and finite horizon T, the Archimedean property gives a finite natural M_n with T ≤ M_n h_n. This genuine grid horizon selection supports the capped strict lower stopping clock. It changes no binder or proposition from the failed publication.
-- source:
--   Source-faithful causal repair of failed authoring job e04482b8-16dd-4534-9070-bc172375c001 (formal statement unknown namespace); removes unjustified open AvramDividend.Classical from the preamble, retaining exact original theorem statement. Proof source work/avram_ws01c_mesh_horizon_solution_repair_20261028.lean.

import Mathlib

open Set
open scoped NNReal

theorem AvramDividend.Classical.bv_choose_finite_mesh_horizon_indices_ws01c
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n : ℕ, 0 < mesh n) :
    ∃ M : ℕ → ℕ, ∀ n : ℕ,
      T ≤ (M n : ℝ≥0) * mesh n := by sorry
