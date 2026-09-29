-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_norm_sub_proj_le_of_mem_range
-- name    : BookProof.ChapterSirkGramCutoff.norm_sub_proj_le_of_mem_range
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:41:16.164874+00:00
-- url     : https://prove2.me/theorems/bd433191-a21b-4f20-b431-8de7b4542f77
-- title:
--   {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (V : F →L[ℂ] E) (hV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F) (x : E) {y : E} (hy : ∃ z, V z = y) : ‖x - V...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.norm_sub_proj_le_of_mem_range` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.norm_sub_proj_le_of_mem_range
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

theorem BookProof.ChapterSirkGramCutoff.norm_sub_proj_le_of_mem_range {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (V : F →L[ℂ] E)
    (hV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F)
    (x : E) {y : E} (hy : ∃ z, V z = y) :
    ‖x - V (adjoint V x)‖ ≤ ‖x - y‖ := by sorry
