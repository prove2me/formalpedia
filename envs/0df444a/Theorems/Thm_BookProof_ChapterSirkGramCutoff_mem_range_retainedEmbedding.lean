-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_mem_range_retainedEmbedding
-- name    : BookProof.ChapterSirkGramCutoff.mem_range_retainedEmbedding
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:20:28.630314+00:00
-- url     : https://prove2.me/theorems/bf79a2f2-150a-4c68-a8a4-88e8ae160447
-- title:
--   {d : ℕ} {e : Fin d → Fin m} (hpos : ∀ j : Fin d, 0 < lam (e j)) (j : Fin d) : ∃ z, retainedEmbedding w u lam e z = synthesis w (u (e j))
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.mem_range_retainedEmbedding` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.mem_range_retainedEmbedding
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
open BookProof.ChapterSirkGramCutoff









noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

theorem BookProof.ChapterSirkGramCutoff.mem_range_retainedEmbedding {d : ℕ} {e : Fin d → Fin m}
    (hpos : ∀ j : Fin d, 0 < lam (e j)) (j : Fin d) :
    ∃ z, retainedEmbedding w u lam e z = synthesis w (u (e j)) := by sorry
