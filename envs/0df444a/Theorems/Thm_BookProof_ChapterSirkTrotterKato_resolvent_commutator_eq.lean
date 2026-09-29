-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_resolvent_commutator_eq
-- name    : BookProof.ChapterSirkTrotterKato.resolvent_commutator_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:40:09.664924+00:00
-- url     : https://prove2.me/theorems/fe14eba9-24b3-4d5b-99cc-8febe50c0022
-- title:
--   (T S : UnboundedSelfAdjoint H) (y : T.domain) : S.op ⟨S.resCLM 1 (y : H), S.resCLM_mem 1 (y : H)⟩ - S.resCLM 1 (T.op y) = T.resCLM 1 (T.shift 1 y) - S.resCLM 1 (T.shift 1 y)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.resolvent_commutator_eq` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.resolvent_commutator_eq
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.resolvent_commutator_eq (T S : UnboundedSelfAdjoint H) (y : T.domain) :
    S.op ⟨S.resCLM 1 (y : H), S.resCLM_mem 1 (y : H)⟩ - S.resCLM 1 (T.op y)
      = T.resCLM 1 (T.shift 1 y) - S.resCLM 1 (T.shift 1 y) := by sorry
