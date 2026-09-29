-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_sirk_end_to_end_satisfiable
-- name    : BookProof.ChapterSirkEndToEnd.sirk_end_to_end_satisfiable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:48:13.479844+00:00
-- url     : https://prove2.me/theorems/63a7dee5-4453-42f0-b7d6-c5511f07302b
-- title:
--   (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖) (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y)...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.sirk_end_to_end_satisfiable` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.sirk_end_to_end_satisfiable
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.sirk_end_to_end_satisfiable
    (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y)
    (m : ℕ) (v : E) (hv : V (V.adjoint v) = v) :
    ‖X v - sirkApprox V (compress V X) v‖ ≤ sirkBound 1 1 1 ‖v‖ m := by sorry
