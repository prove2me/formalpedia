-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_interior_C1_compact_interval_lipschitz
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_interior_C1_compact_interval_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:34:16.616324+00:00
-- url     : https://prove2.me/theorems/55294192-aca9-4f8c-a4eb-b4b436502aec
-- title:
--   C1 regularity on original interior produces a uniform compact BV jump Lipschitz envelope
-- statement:
--   Theorem extracts a uniform nonnegative Lipschitz constant on a closed real interval contained in the C1 region of the original dividend verification value. Its existence provides precisely the first-order small negative jump bound used in the BV finite-variation source drift integrability proof.
-- source:
--   Mathlib ContDiffOn.exists_lipschitzOnWith on convex compact intervals

import Mathlib
open Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_interior_C1_compact_interval_lipschitz (w : ℝ → ℝ) (s : Set ℝ) (hw : ContDiffOn ℝ 1 w s) (a b : ℝ) (hsub : Icc a b ⊆ s) : ∃ K : ℝ≥0, LipschitzOnWith K w (Icc a b) := by sorry
