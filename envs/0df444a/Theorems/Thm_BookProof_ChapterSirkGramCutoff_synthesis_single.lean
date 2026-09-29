-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_synthesis_single
-- name    : BookProof.ChapterSirkGramCutoff.synthesis_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:23:12.973745+00:00
-- url     : https://prove2.me/theorems/e6fd0ac4-d8fb-4fae-a86c-dbf8f51ee33e
-- title:
--   (i : Fin m) : synthesis w (EuclideanSpace.single i (1 : ℂ)) = w i
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.synthesis_single` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.synthesis_single
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

theorem BookProof.ChapterSirkGramCutoff.synthesis_single (i : Fin m) :
    synthesis w (EuclideanSpace.single i (1 : ℂ)) = w i := by sorry
