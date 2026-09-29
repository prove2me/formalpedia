-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_resCLM_ofBounded
-- name    : BookProof.ChapterSirkTrotterKato.resCLM_ofBounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:16:44.916796+00:00
-- url     : https://prove2.me/theorems/662b59e0-80c8-48b6-967f-cd9acf8b35c6
-- title:
--   (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (y : H) : (ofBounded A hA).resCLM 1 y = -(resolvent A Complex.I y)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.resCLM_ofBounded` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — theorem BookProof.ChapterSirkTrotterKato.resCLM_ofBounded
import Mathlib
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
open BookProof.ChapterSirkTrotterKato








noncomputable section

open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.resCLM_ofBounded (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (y : H) :
    (ofBounded A hA).resCLM 1 y = -(resolvent A Complex.I y) := by sorry
