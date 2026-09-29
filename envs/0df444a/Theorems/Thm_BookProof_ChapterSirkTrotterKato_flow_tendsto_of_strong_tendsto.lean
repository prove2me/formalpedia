-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_flow_tendsto_of_strong_tendsto
-- name    : BookProof.ChapterSirkTrotterKato.flow_tendsto_of_strong_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:05.941277+00:00
-- url     : https://prove2.me/theorems/0fc2e632-ad93-410c-a845-1e258edb1584
-- title:
--   {A : ℕ → H →L[ℂ] H} {Alim : H →L[ℂ] H} (hA : ∀ n, IsSelfAdjoint (A n)) (hlim : IsSelfAdjoint Alim) (hconv : ∀ u : H, Tendsto (fun n => A n u) atTop (𝓝 (Alim u))) (v : H) (t :...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.flow_tendsto_of_strong_tendsto` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — theorem BookProof.ChapterSirkTrotterKato.flow_tendsto_of_strong_tendsto
import Mathlib
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
open BookProof.ChapterSirkTrotterKato








noncomputable section

open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.flow_tendsto_of_strong_tendsto {A : ℕ → H →L[ℂ] H} {Alim : H →L[ℂ] H}
    (hA : ∀ n, IsSelfAdjoint (A n)) (hlim : IsSelfAdjoint Alim)
    (hconv : ∀ u : H, Tendsto (fun n => A n u) atTop (𝓝 (Alim u))) (v : H) (t : ℝ) :
    Tendsto (fun n => (ofBounded (A n) (hA n)).stoneU t v) atTop
      (𝓝 ((ofBounded Alim hlim).stoneU t v)) := by sorry
