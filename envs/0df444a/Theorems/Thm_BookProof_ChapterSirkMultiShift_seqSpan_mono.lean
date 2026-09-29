-- Prove2me | Theorems.Thm_BookProof_ChapterSirkMultiShift_seqSpan_mono
-- name    : BookProof.ChapterSirkMultiShift.seqSpan_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:35:20.286802+00:00
-- url     : https://prove2.me/theorems/29706405-976a-4b40-92fb-4543ead4771d
-- title:
--   (u : ℕ → E) {m n : ℕ} (hmn : m ≤ n) : seqSpan (K
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkMultiShift.seqSpan_mono` (module `BookProof.ChapterSirkMultiShift`), source chapter `BookProof/ChapterChapterSirkMultiShift.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkMultiShift.lean

-- Generated from ChapterSirkMultiShift.lean — theorem BookProof.ChapterSirkMultiShift.seqSpan_mono
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift










noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem BookProof.ChapterSirkMultiShift.seqSpan_mono (u : ℕ → E) {m n : ℕ} (hmn : m ≤ n) :
    seqSpan (K := K) u m ≤ seqSpan (K := K) u n := by sorry
