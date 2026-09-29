-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_hasDerivAt_stoneU_const_sub
-- name    : BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:37:39.571524+00:00
-- url     : https://prove2.me/theorems/70c89f9c-8dee-4545-b9cf-bb077f87151c
-- title:
--   (S : UnboundedSelfAdjoint H) (z : S.domain) (t u : ℝ) : HasDerivAt (fun r : ℝ => S.stoneU (t - r) (z : H)) (Complex.I • S.op ⟨S.stoneU (t - u) (z : H), S.stoneU_mem_domain (t - u) z⟩) u
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub (S : UnboundedSelfAdjoint H) (z : S.domain) (t u : ℝ) :
    HasDerivAt (fun r : ℝ => S.stoneU (t - r) (z : H))
      (Complex.I • S.op ⟨S.stoneU (t - u) (z : H), S.stoneU_mem_domain (t - u) z⟩) u := by sorry
