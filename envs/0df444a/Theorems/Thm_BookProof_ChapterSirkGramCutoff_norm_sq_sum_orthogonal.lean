-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_norm_sq_sum_orthogonal
-- name    : BookProof.ChapterSirkGramCutoff.norm_sq_sum_orthogonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:21:03.544352+00:00
-- url     : https://prove2.me/theorems/4f38d37e-cd5e-4d37-b110-ef0440eb782a
-- title:
--   {m : ℕ} (y : Fin m → E) (lam : Fin m → ℝ) (h : ∀ k l, ⟪y k, y l⟫_ℂ = if k = l then (lam l : ℂ) else 0) (s : Finset (Fin m)) (a : Fin m → ℂ) : ‖∑ k ∈ s, a k • y k‖ ^ 2 = ∑ k ∈ s, ‖a k‖ ^ 2 * lam k
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.norm_sq_sum_orthogonal` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.norm_sq_sum_orthogonal
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
open BookProof.ChapterSirkGramCutoff









noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramCutoff.norm_sq_sum_orthogonal {m : ℕ} (y : Fin m → E) (lam : Fin m → ℝ)
    (h : ∀ k l, ⟪y k, y l⟫_ℂ = if k = l then (lam l : ℂ) else 0)
    (s : Finset (Fin m)) (a : Fin m → ℂ) :
    ‖∑ k ∈ s, a k • y k‖ ^ 2 = ∑ k ∈ s, ‖a k‖ ^ 2 * lam k := by sorry
