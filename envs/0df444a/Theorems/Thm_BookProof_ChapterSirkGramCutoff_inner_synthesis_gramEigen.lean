-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_inner_synthesis_gramEigen
-- name    : BookProof.ChapterSirkGramCutoff.inner_synthesis_gramEigen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:19:42.085203+00:00
-- url     : https://prove2.me/theorems/50802eca-b0d2-4668-a6e7-3a2bcb598866
-- title:
--   (heig : IsGramEigen w u lam) (k l : Fin m) : ⟪synthesis w (u k), synthesis w (u l)⟫_ℂ = if k = l then (lam l : ℂ) else 0
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.inner_synthesis_gramEigen` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.inner_synthesis_gramEigen
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

theorem BookProof.ChapterSirkGramCutoff.inner_synthesis_gramEigen (heig : IsGramEigen w u lam) (k l : Fin m) :
    ⟪synthesis w (u k), synthesis w (u l)⟫_ℂ = if k = l then (lam l : ℂ) else 0 := by sorry
