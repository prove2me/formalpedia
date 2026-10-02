-- Prove2me | Theorems.Thm_BookProof_ChapterH6_reduceGenerator_eq_compress_entry
-- name    : BookProof.ChapterH6.reduceGenerator_eq_compress_entry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T18:30:41.794179+00:00
-- url     : https://prove2.me/theorems/28e5ff55-c4c1-4eb1-ba03-27ec0e66db5f
-- title:
--   The Lean 4 theorem `reduceGenerator_eq_compress_entry` in the `ChapterH6` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `reduceGenerator_eq_compress_entry` in the `ChapterH6` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH6.lean

-- Generated from ChapterH6.lean — theorem BookProof.ChapterH6.reduceGenerator_eq_compress_entry
import Mathlib
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4
open BookProof.ChapterH4
open BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


noncomputable section

open Filter Topology

theorem BookProof.ChapterH6.reduceGenerator_eq_compress_entry (m : ℕ)
    (V : EuclideanSpace ℂ (Fin m) →L[ℂ] E) (X : E →L[ℂ] E) (i j : Fin m) :
    reduceGenerator m V X i j
      = inner ℂ (EuclideanSpace.single i (1 : ℂ))
          (compress V X (EuclideanSpace.single j (1 : ℂ))) := by sorry
