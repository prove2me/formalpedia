-- Prove2me | Theorems.Thm_BookProof_ChapterH8_orthonormalEmbedding_inner
-- name    : BookProof.ChapterH8.orthonormalEmbedding_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T21:49:13.046313+00:00
-- url     : https://prove2.me/theorems/ece0ba63-4071-460b-8495-3bdbdba7844f
-- title:
--   The Lean 4 theorem `orthonormalEmbedding_inner` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `orthonormalEmbedding_inner` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.orthonormalEmbedding_inner
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

theorem BookProof.ChapterH8.orthonormalEmbedding_inner {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w)
    (x y : EuclideanSpace ℂ (Fin m)) :
    inner ℂ (orthonormalEmbedding w hw x) (orthonormalEmbedding w hw y) = inner ℂ x y := by sorry
