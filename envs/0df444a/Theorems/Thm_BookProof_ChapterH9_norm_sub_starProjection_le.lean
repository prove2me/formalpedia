-- Prove2me | Theorems.Thm_BookProof_ChapterH9_norm_sub_starProjection_le
-- name    : BookProof.ChapterH9.norm_sub_starProjection_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:39:11.184574+00:00
-- url     : https://prove2.me/theorems/7b03e853-1035-4c84-a62d-754a91a9dcda
-- title:
--   The Lean 4 theorem `norm_sub_starProjection_le` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_sub_starProjection_le` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.norm_sub_starProjection_le
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

theorem BookProof.ChapterH9.norm_sub_starProjection_le (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (u w : E) (hw : w ∈ K) : ‖u - K.starProjection u‖ ≤ ‖u - w‖ := by sorry
