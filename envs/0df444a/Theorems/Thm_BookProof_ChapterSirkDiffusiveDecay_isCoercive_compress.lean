-- Prove2me | Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_isCoercive_compress
-- name    : BookProof.ChapterSirkDiffusiveDecay.isCoercive_compress
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-09T12:07:17.274222+00:00
-- url     : https://prove2.me/theorems/69b6b476-3e98-46af-85a6-327bcd910ddc
-- title:
--   ChapterSirkDiffusiveDecay theorem
-- statement:
--   Theorem from ChapterSirkDiffusiveDecay.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkDiffusiveDecay.lean

-- Generated from ChapterSirkDiffusiveDecay.lean — theorem BookProof.ChapterSirkDiffusiveDecay.isCoercive_compress
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
open BookProof.ChapterSirkDiffusiveDecay









noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkDiffusiveDecay.isCoercive_compress (V : F →L[ℂ] E) (A : E →L[ℂ] E) {mu : ℝ}
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (hA : IsCoercive A mu) :
    IsCoercive (compress V A) mu := by sorry
