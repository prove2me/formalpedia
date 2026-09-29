-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_norm_sq_synthesis_gramEigen
-- name    : BookProof.ChapterSirkGramCutoff.norm_sq_synthesis_gramEigen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:42:57.808867+00:00
-- url     : https://prove2.me/theorems/40703e0c-19f9-4b26-a703-8aa0025ee96a
-- title:
--   (heig : IsGramEigen w u lam) (k : Fin m) : ‖synthesis w (u k)‖ ^ 2 = lam k
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.norm_sq_synthesis_gramEigen` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.norm_sq_synthesis_gramEigen
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

theorem BookProof.ChapterSirkGramCutoff.norm_sq_synthesis_gramEigen (heig : IsGramEigen w u lam) (k : Fin m) :
    ‖synthesis w (u k)‖ ^ 2 = lam k := by sorry
