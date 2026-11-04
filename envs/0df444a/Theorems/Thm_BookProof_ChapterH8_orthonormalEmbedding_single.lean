-- Prove2me | Theorems.Thm_BookProof_ChapterH8_orthonormalEmbedding_single
-- name    : BookProof.ChapterH8.orthonormalEmbedding_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T21:49:23.249989+00:00
-- url     : https://prove2.me/theorems/5623a9a9-61da-415a-a62f-4ae231375bb9
-- title:
--   The Lean 4 theorem `orthonormalEmbedding_single` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `orthonormalEmbedding_single` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.orthonormalEmbedding_single
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

theorem BookProof.ChapterH8.orthonormalEmbedding_single {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w) (i : Fin m) :
    orthonormalEmbedding w hw (EuclideanSpace.single i (1 : ℂ)) = w i := by sorry
