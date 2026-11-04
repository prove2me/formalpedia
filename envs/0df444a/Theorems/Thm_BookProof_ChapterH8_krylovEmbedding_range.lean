-- Prove2me | Theorems.Thm_BookProof_ChapterH8_krylovEmbedding_range
-- name    : BookProof.ChapterH8.krylovEmbedding_range
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-03T21:50:28.900418+00:00
-- url     : https://prove2.me/theorems/1cd99fc8-bf81-46f2-b858-f3a16b13b60c
-- title:
--   The Lean 4 theorem `krylovEmbedding_range` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `krylovEmbedding_range` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.krylovEmbedding_range
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterH5
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

theorem BookProof.ChapterH8.krylovEmbedding_range (H : E →ₗ[ℂ] E) (v : E) {n : ℕ}
    (hli : LinearIndependent ℂ (fun i : Fin n => (H ^ (i : ℕ)) v)) :
    LinearMap.range (krylovEmbedding H v hli : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] E)
      = krylovSpan H v n := by sorry
