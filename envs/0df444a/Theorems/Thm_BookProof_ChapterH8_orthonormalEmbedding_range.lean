-- Prove2me | Theorems.Thm_BookProof_ChapterH8_orthonormalEmbedding_range
-- name    : BookProof.ChapterH8.orthonormalEmbedding_range
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T21:49:43.488047+00:00
-- url     : https://prove2.me/theorems/791a139e-9a19-4a33-bd62-b57adfd5b513
-- title:
--   The Lean 4 theorem `orthonormalEmbedding_range` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `orthonormalEmbedding_range` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.orthonormalEmbedding_range
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

theorem BookProof.ChapterH8.orthonormalEmbedding_range {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w) :
    LinearMap.range (orthonormalEmbedding w hw : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
      = Submodule.span ℂ (Set.range w) := by sorry
