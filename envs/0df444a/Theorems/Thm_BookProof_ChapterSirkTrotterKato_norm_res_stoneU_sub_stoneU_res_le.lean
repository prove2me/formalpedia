-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_norm_res_stoneU_sub_stoneU_res_le
-- name    : BookProof.ChapterSirkTrotterKato.norm_res_stoneU_sub_stoneU_res_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:15:43.05569+00:00
-- url     : https://prove2.me/theorems/27fc35b7-bd04-4ee8-9e12-ebd829bbf18c
-- title:
--   (T S : UnboundedSelfAdjoint H) (chi : T.domain) (t : ℝ) {C : ℝ} (hC : ∀ s ∈ Set.uIcc (0 : ℝ) t, ‖T.resCLM 1 (T.stoneU s (T.shift 1 chi)) - S.resCLM 1 (T.stoneU s (T.shift 1 chi))‖...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.norm_res_stoneU_sub_stoneU_res_le` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.norm_res_stoneU_sub_stoneU_res_le
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSirkTrotterKato.norm_res_stoneU_sub_stoneU_res_le (T S : UnboundedSelfAdjoint H) (chi : T.domain)
    (t : ℝ) {C : ℝ}
    (hC : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      ‖T.resCLM 1 (T.stoneU s (T.shift 1 chi)) - S.resCLM 1 (T.stoneU s (T.shift 1 chi))‖ ≤ C) :
    ‖S.resCLM 1 (T.stoneU t (chi : H)) - S.stoneU t (S.resCLM 1 (chi : H))‖ ≤ C * |t| := by sorry
