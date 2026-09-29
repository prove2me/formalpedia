-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_sirk_flow_error_tendsto_zero
-- name    : BookProof.ChapterSirkEndToEnd.sirk_flow_error_tendsto_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:40:07.969248+00:00
-- url     : https://prove2.me/theorems/8effc819-7ba1-4ed2-b6a8-4ae1adee2416
-- title:
--   {G : ℕ → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)] [∀ m, CompleteSpace (G m)] (flow : E →L[ℂ] E) (V : ∀ m, G m →L[ℂ] E) (psiB : ∀ m, G m →L[ℂ] G m) (C Dmin h : ℝ) (hh...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.sirk_flow_error_tendsto_zero` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.sirk_flow_error_tendsto_zero
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.sirk_flow_error_tendsto_zero
    {G : ℕ → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)]
    [∀ m, CompleteSpace (G m)]
    (flow : E →L[ℂ] E) (V : ∀ m, G m →L[ℂ] E) (psiB : ∀ m, G m →L[ℂ] G m)
    (C Dmin h : ℝ) (hh : 0 < h) (v : E)
    (hbound : ∀ m, ‖flow v - sirkApprox (V m) (psiB m) v‖ ≤ sirkBound C Dmin h ‖v‖ m) :
    Tendsto (fun m => ‖flow v - sirkApprox (V m) (psiB m) v‖) atTop (𝓝 0) := by sorry
