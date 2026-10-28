-- Prove2me | Theorems.Thm_BookProof_ChapterH8_orthonormalEmbedding_adjoint_comp
-- name    : BookProof.ChapterH8.orthonormalEmbedding_adjoint_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T03:22:49.158147+00:00
-- url     : https://prove2.me/theorems/ab402e01-bba5-4d99-b2d3-4daa1d45cccb
-- title:
--   The Lean 4 theorem `orthonormalEmbedding_adjoint_comp` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `orthonormalEmbedding_adjoint_comp` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.orthonormalEmbedding_adjoint_comp
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

theorem BookProof.ChapterH8.orthonormalEmbedding_adjoint_comp {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w) :
    (adjoint (orthonormalEmbedding w hw)).comp (orthonormalEmbedding w hw)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) := by sorry
