-- Prove2me | Theorems.Thm_BookProof_ChapterH6_reduce_generator_mul_m
-- name    : BookProof.ChapterH6.reduce_generator_mul_m
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:42:21.476074+00:00
-- url     : https://prove2.me/theorems/828a8e60-9a49-4eca-84f3-b9c59ec37711
-- title:
--   The Lean 4 theorem `reduce_generator_mul_m` in the `ChapterH6` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `reduce_generator_mul_m` in the `ChapterH6` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH6.lean

-- Generated from ChapterH6.lean — theorem BookProof.ChapterH6.reduce_generator_mul_m
import Mathlib
import Definitions.Def_ChapterH6
open BookProof.ChapterH6


noncomputable section

open Filter Topology

theorem BookProof.ChapterH6.reduce_generator_mul_m (m : ℕ) : Fintype.card (Fin m × Fin m) = m * m := by sorry
