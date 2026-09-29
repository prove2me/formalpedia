-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_exists_gramEigen
-- name    : BookProof.ChapterSirkGramCutoff.exists_gramEigen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:18:34.760949+00:00
-- url     : https://prove2.me/theorems/5e579a08-a318-4f37-be54-8726a1545fe3
-- title:
--   {m : ℕ} (w : Fin m → E) : ∃ (u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (lam : Fin m → ℝ), IsGramEigen w u lam
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.exists_gramEigen` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.exists_gramEigen
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
open BookProof.ChapterSirkGramCutoff









noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramCutoff.exists_gramEigen {m : ℕ} (w : Fin m → E) :
    ∃ (u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (lam : Fin m → ℝ),
      IsGramEigen w u lam := by sorry
