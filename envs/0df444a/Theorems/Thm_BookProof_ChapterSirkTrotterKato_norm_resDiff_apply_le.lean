-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTrotterKato_norm_resDiff_apply_le
-- name    : BookProof.ChapterSirkTrotterKato.norm_resDiff_apply_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:39:30.810185+00:00
-- url     : https://prove2.me/theorems/cdff2298-af67-4904-9caf-e62c37caef9a
-- title:
--   (n : ℕ) (y : H) : ‖resDiff T S n y‖ ≤ 2 * ‖y‖
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTrotterKato.norm_resDiff_apply_le` (module `BookProof.ChapterSirkTrotterKato`), source chapter `BookProof/ChapterChapterSirkTrotterKato.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTrotterKato.lean

-- Generated from ChapterSirkTrotterKato.lean — theorem BookProof.ChapterSirkTrotterKato.norm_resDiff_apply_le
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato










noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

theorem BookProof.ChapterSirkTrotterKato.norm_resDiff_apply_le (n : ℕ) (y : H) : ‖resDiff T S n y‖ ≤ 2 * ‖y‖ := by sorry
