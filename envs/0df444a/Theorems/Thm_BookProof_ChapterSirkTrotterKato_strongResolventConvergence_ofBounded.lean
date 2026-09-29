-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_strongResolventConvergence_ofBounded
-- name    : BookProof.ChapterSirkTrotterKato.strongResolventConvergence_ofBounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:55:48.184395+00:00
-- url     : https://prove2.me/theorems/4510287c-a55a-4b9c-9f82-9b1a544f0668
-- title:
--   {A : ℕ → H →L[ℂ] H} {Alim : H →L[ℂ] H} (hA : ∀ n, IsSelfAdjoint (A n)) (hlim : IsSelfAdjoint Alim) (hconv : ∀ u : H, Tendsto (fun n => A n u) atTop (𝓝 (Alim u))) :...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.strongResolventConvergence_ofBounded` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — theorem BookProof.ChapterSirkTrotterKato.strongResolventConvergence_ofBounded
import Mathlib
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
open BookProof.ChapterSirkTrotterKato








noncomputable section

open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.strongResolventConvergence_ofBounded {A : ℕ → H →L[ℂ] H} {Alim : H →L[ℂ] H}
    (hA : ∀ n, IsSelfAdjoint (A n)) (hlim : IsSelfAdjoint Alim)
    (hconv : ∀ u : H, Tendsto (fun n => A n u) atTop (𝓝 (Alim u))) :
    StrongResolventConvergence (ofBounded Alim hlim) (fun n => ofBounded (A n) (hA n)) := by sorry
