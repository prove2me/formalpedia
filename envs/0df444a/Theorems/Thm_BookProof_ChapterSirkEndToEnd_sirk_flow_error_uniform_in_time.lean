-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_sirk_flow_error_uniform_in_time
-- name    : BookProof.ChapterSirkEndToEnd.sirk_flow_error_uniform_in_time
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:34:18.934746+00:00
-- url     : https://prove2.me/theorems/73e93e13-1681-4429-b849-cf24524b40a2
-- title:
--   {G : ℕ → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)] [∀ m, CompleteSpace (G m)] (flow : ℝ → E →L[ℂ] E) (V : ∀ m, G m →L[ℂ] E) (psiB : ∀ m, ℝ → G m →L[ℂ] G m) (C Dmin h :...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.sirk_flow_error_uniform_in_time` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.sirk_flow_error_uniform_in_time
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.sirk_flow_error_uniform_in_time
    {G : ℕ → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)]
    [∀ m, CompleteSpace (G m)]
    (flow : ℝ → E →L[ℂ] E) (V : ∀ m, G m →L[ℂ] E) (psiB : ∀ m, ℝ → G m →L[ℂ] G m)
    (C Dmin h : ℝ) (hh : 0 < h) (v : E)
    (hbound : ∀ (t : ℝ) (m : ℕ),
      ‖flow t v - sirkApprox (V m) (psiB m t) v‖ ≤ sirkBound C Dmin h ‖v‖ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ t : ℝ, ‖flow t v - sirkApprox (V m) (psiB m t) v‖ < ε := by sorry
