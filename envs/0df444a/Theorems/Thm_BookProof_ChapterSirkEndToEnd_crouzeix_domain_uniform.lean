-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_crouzeix_domain_uniform
-- name    : BookProof.ChapterSirkEndToEnd.crouzeix_domain_uniform
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:09:26.010853+00:00
-- url     : https://prove2.me/theorems/c623b567-2b42-4b8a-a449-d6646c14d8e7
-- title:
--   (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) : (convexHull ℝ) (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) ‖X‖
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.crouzeix_domain_uniform` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.crouzeix_domain_uniform
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.crouzeix_domain_uniform (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) :
    (convexHull ℝ) (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) ‖X‖ := by sorry
