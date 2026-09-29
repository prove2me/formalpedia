-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_ofBounded_op
-- name    : BookProof.ChapterSirkTrotterKato.ofBounded_op
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:16:08.912873+00:00
-- url     : https://prove2.me/theorems/4cad9df3-b1ee-42df-8a0d-d463157df58d
-- title:
--   (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) (hx : x ∈ (ofBounded A hA).domain) : (ofBounded A hA).op ⟨x, hx⟩ = A x
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.ofBounded_op` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — theorem BookProof.ChapterSirkTrotterKato.ofBounded_op
import Mathlib
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
open BookProof.ChapterSirkTrotterKato








noncomputable section

open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.ofBounded_op (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H)
    (hx : x ∈ (ofBounded A hA).domain) : (ofBounded A hA).op ⟨x, hx⟩ = A x := by sorry
