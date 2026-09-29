-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_stoneU_shift
-- name    : BookProof.ChapterSirkTrotterKato.stoneU_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:40:54.683433+00:00
-- url     : https://prove2.me/theorems/403eb9e1-9eee-4e3e-b654-664a358d8111
-- title:
--   (T : UnboundedSelfAdjoint H) (chi : T.domain) (u : ℝ) : T.shift 1 ⟨T.stoneU u (chi : H), T.stoneU_mem_domain u chi⟩ = T.stoneU u (T.shift 1 chi)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.stoneU_shift` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.stoneU_shift
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.stoneU_shift (T : UnboundedSelfAdjoint H) (chi : T.domain) (u : ℝ) :
    T.shift 1 ⟨T.stoneU u (chi : H), T.stoneU_mem_domain u chi⟩
      = T.stoneU u (T.shift 1 chi) := by sorry
