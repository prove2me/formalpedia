-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_range_retainedEmbedding
-- name    : BookProof.ChapterSirkGramCutoff.range_retainedEmbedding
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:49:39.178606+00:00
-- url     : https://prove2.me/theorems/1ec0f3ee-1abc-40ac-82cc-c47d0a8d46e2
-- title:
--   {d : ℕ} (w : Fin m → E) (u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (lam : Fin m → ℝ) (e : Fin d → Fin m) : LinearMap.range (retainedEmbedding w u lam e : EuclideanSpace ℂ (Fin d)...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.range_retainedEmbedding` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.range_retainedEmbedding
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

theorem BookProof.ChapterSirkGramCutoff.range_retainedEmbedding {d : ℕ} (w : Fin m → E)
    (u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (lam : Fin m → ℝ)
    (e : Fin d → Fin m) :
    LinearMap.range (retainedEmbedding w u lam e :
        EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E)
      = Submodule.span ℂ (Set.range (retainedVec w u lam e)) := by sorry
