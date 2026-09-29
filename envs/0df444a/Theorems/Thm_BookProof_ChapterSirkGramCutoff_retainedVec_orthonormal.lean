-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_retainedVec_orthonormal
-- name    : BookProof.ChapterSirkGramCutoff.retainedVec_orthonormal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:43:41.330901+00:00
-- url     : https://prove2.me/theorems/86d5195b-1406-4e96-981b-1e130d421827
-- title:
--   (heig : IsGramEigen w u lam) {d : ℕ} {e : Fin d → Fin m} (he : Function.Injective e) (hpos : ∀ j, 0 < lam (e j)) : Orthonormal ℂ (retainedVec w u lam e)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.retainedVec_orthonormal` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.retainedVec_orthonormal
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

theorem BookProof.ChapterSirkGramCutoff.retainedVec_orthonormal (heig : IsGramEigen w u lam) {d : ℕ} {e : Fin d → Fin m}
    (he : Function.Injective e) (hpos : ∀ j, 0 < lam (e j)) :
    Orthonormal ℂ (retainedVec w u lam e) := by sorry
