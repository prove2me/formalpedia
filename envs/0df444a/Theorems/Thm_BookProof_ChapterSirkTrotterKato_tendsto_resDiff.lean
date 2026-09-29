-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_tendsto_resDiff
-- name    : BookProof.ChapterSirkTrotterKato.tendsto_resDiff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:41:27.277382+00:00
-- url     : https://prove2.me/theorems/a7e02146-f315-40f3-9168-c38f3b8b2a62
-- title:
--   (hres : StrongResolventConvergence T S) (y : H) : Tendsto (fun n => resDiff T S n y) atTop (𝓝 0)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.tendsto_resDiff` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.tendsto_resDiff
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

theorem BookProof.ChapterSirkTrotterKato.tendsto_resDiff (hres : StrongResolventConvergence T S) (y : H) :
    Tendsto (fun n => resDiff T S n y) atTop (𝓝 0) := by sorry
