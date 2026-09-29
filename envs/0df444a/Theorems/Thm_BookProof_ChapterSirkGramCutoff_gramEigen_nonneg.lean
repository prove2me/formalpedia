-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_gramEigen_nonneg
-- name    : BookProof.ChapterSirkGramCutoff.gramEigen_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:54:06.192724+00:00
-- url     : https://prove2.me/theorems/fe06da78-cabf-43df-ae16-ec897f367b93
-- title:
--   (heig : IsGramEigen w u lam) (k : Fin m) : 0 ≤ lam k
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.gramEigen_nonneg` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.gramEigen_nonneg
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

theorem BookProof.ChapterSirkGramCutoff.gramEigen_nonneg (heig : IsGramEigen w u lam) (k : Fin m) : 0 ≤ lam k := by sorry
