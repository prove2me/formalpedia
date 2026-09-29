-- Prove2me | Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_isCoercive_add_algebraMap
-- name    : BookProof.ChapterSirkDiffusiveDecay.isCoercive_add_algebraMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-09T12:06:41.196557+00:00
-- url     : https://prove2.me/theorems/ab3e55d9-63f3-473c-b471-d3f56b792b2d
-- title:
--   ChapterSirkDiffusiveDecay theorem
-- statement:
--   Theorem from ChapterSirkDiffusiveDecay.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkDiffusiveDecay.lean

-- Generated from ChapterSirkDiffusiveDecay.lean — theorem BookProof.ChapterSirkDiffusiveDecay.isCoercive_add_algebraMap
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
open BookProof.ChapterSirkDiffusiveDecay









noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkDiffusiveDecay.isCoercive_add_algebraMap (B : E →L[ℂ] E) (mu : ℝ)
    (hB : ∀ x : E, 0 ≤ (inner ℂ x (B x) : ℂ).re) :
    IsCoercive (B + (algebraMap ℝ (E →L[ℂ] E)) mu) mu := by sorry
