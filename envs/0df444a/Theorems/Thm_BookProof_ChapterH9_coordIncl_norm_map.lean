-- Prove2me | Theorems.Thm_BookProof_ChapterH9_coordIncl_norm_map
-- name    : BookProof.ChapterH9.coordIncl_norm_map
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:20:30.96309+00:00
-- url     : https://prove2.me/theorems/c4aaacec-e90f-449c-849d-7ffc29f71d62
-- title:
--   The Lean 4 theorem `coordIncl_norm_map` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coordIncl_norm_map` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.coordIncl_norm_map
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9


noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterH9.coordIncl_norm_map {m n : ℕ} (hmn : m ≤ n) (x : EuclideanSpace ℂ (Fin m)) :
    ‖coordIncl hmn x‖ = ‖x‖ := by sorry
