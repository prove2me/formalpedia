-- Prove2me | Theorems.Thm_BookProof_ChapterH9_norm_sub_starProjection_antitone
-- name    : BookProof.ChapterH9.norm_sub_starProjection_antitone
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:21:03.352992+00:00
-- url     : https://prove2.me/theorems/fbf502a6-fada-409d-ad46-63a86127e833
-- title:
--   The Lean 4 theorem `norm_sub_starProjection_antitone` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_sub_starProjection_antitone` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.norm_sub_starProjection_antitone
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

theorem BookProof.ChapterH9.norm_sub_starProjection_antitone (K L : Submodule ℂ E)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L) (v : E) :
    ‖v - L.starProjection v‖ ≤ ‖v - K.starProjection v‖ := by sorry
