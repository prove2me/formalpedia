-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_leakageIter_succ
-- name    : BookProof.BrstLeakage.leakageIter_succ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:11:36.74328+00:00
-- url     : https://prove2.me/theorems/07882f02-dd45-46f3-a1ee-09462e78a1b0
-- title:
--   `BookProof.BrstLeakage.leakageIter_succ` (B : ℕ → E →L[ℂ] E) (τ : ℝ) (x : E) (n : ℕ) : leakageIter B τ x (n + 1) = flow (B n) τ (leakageIter B τ x n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.leakageIter_succ` (B : ℕ → E →L[ℂ] E) (τ : ℝ) (x : E) (n : ℕ) : leakageIter B τ x (n + 1) = flow (B n) τ (leakageIter B τ x n)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.leakageIter_succ`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.leakageIter_succ
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.leakageIter_succ (B : ℕ → E →L[ℂ] E) (τ : ℝ) (x : E) (n : ℕ) :
    leakageIter B τ x (n + 1) = flow (B n) τ (leakageIter B τ x n) := by sorry
