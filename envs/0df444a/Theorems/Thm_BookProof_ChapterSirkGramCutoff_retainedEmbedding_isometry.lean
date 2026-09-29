-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_retainedEmbedding_isometry
-- name    : BookProof.ChapterSirkGramCutoff.retainedEmbedding_isometry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T08:00:58.097672+00:00
-- url     : https://prove2.me/theorems/cfc3cd23-8b4e-459d-9bd3-e0eba34f2a34
-- title:
--   (heig : IsGramEigen w u lam) {d : ℕ} {e : Fin d → Fin m} (he : Function.Injective e) (hpos : ∀ j, 0 < lam (e j)) : (adjoint (retainedEmbedding w u lam e)).comp (retainedEmbedding w u lam e)...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.retainedEmbedding_isometry` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.retainedEmbedding_isometry
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

theorem BookProof.ChapterSirkGramCutoff.retainedEmbedding_isometry (heig : IsGramEigen w u lam) {d : ℕ} {e : Fin d → Fin m}
    (he : Function.Injective e) (hpos : ∀ j, 0 < lam (e j)) :
    (adjoint (retainedEmbedding w u lam e)).comp (retainedEmbedding w u lam e)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)) := by sorry
