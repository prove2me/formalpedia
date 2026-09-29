-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_crouzeix_domain_transfer
-- name    : BookProof.ChapterSirkEndToEnd.crouzeix_domain_transfer
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:44:39.418125+00:00
-- url     : https://prove2.me/theorems/e1823a15-0918-4702-afd7-0399e1d82cf6
-- title:
--   (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (S : Set ℂ) (hconv : Convex ℝ S) (hS : numRange X ⊆ S) : (convexHull ℝ) (numRange (compress V X)) ⊆ S
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.crouzeix_domain_transfer` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.crouzeix_domain_transfer
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.crouzeix_domain_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (S : Set ℂ) (hconv : Convex ℝ S)
    (hS : numRange X ⊆ S) :
    (convexHull ℝ) (numRange (compress V X)) ⊆ S := by sorry
