-- Prove2me | Theorems.Thm_BookProof_ChapterH8_krylovOrthonormal_span
-- name    : BookProof.ChapterH8.krylovOrthonormal_span
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-03T21:47:44.201563+00:00
-- url     : https://prove2.me/theorems/fa2f2c23-1013-4d83-8fa8-f5e64c0630f7
-- title:
--   The Lean 4 theorem `krylovOrthonormal_span` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `krylovOrthonormal_span` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.krylovOrthonormal_span
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

theorem BookProof.ChapterH8.krylovOrthonormal_span (H : E →ₗ[ℂ] E) (v : E) (n : ℕ) :
    Submodule.span ℂ (Set.range (fun i : Fin n => krylovOrthonormalSeq H v (i : ℕ)))
      = krylovSpan H v n := by sorry
