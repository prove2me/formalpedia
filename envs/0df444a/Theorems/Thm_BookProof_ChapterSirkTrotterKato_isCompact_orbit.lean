-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_isCompact_orbit
-- name    : BookProof.ChapterSirkTrotterKato.isCompact_orbit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:38:57.158565+00:00
-- url     : https://prove2.me/theorems/c99cc34f-6462-496b-9eaf-b010f3124b5c
-- title:
--   (y : H) (T₀ : ℝ) : IsCompact ((fun s : ℝ => T.stoneU s y) '' Set.Icc (-T₀) T₀)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.isCompact_orbit` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.isCompact_orbit
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

theorem BookProof.ChapterSirkTrotterKato.isCompact_orbit (y : H) (T₀ : ℝ) :
    IsCompact ((fun s : ℝ => T.stoneU s y) '' Set.Icc (-T₀) T₀) := by sorry
