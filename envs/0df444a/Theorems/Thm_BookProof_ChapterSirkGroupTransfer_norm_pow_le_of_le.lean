-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGroupTransfer_norm_pow_le_of_le
-- name    : BookProof.ChapterSirkGroupTransfer.norm_pow_le_of_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T03:29:50.86099+00:00
-- url     : https://prove2.me/theorems/631799c9-817c-452b-9eb5-54117cfae1e9
-- title:
--   The Lean 4 theorem `norm_pow_le_of_le` in the `ChapterSirkGroupTransfer` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_pow_le_of_le` in the `ChapterSirkGroupTransfer` chapter of the timepiece formalization.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterSirkGroupTransfer.norm_pow_le_of_le` (module `BookProof.SirkGroupTransfer`), line-linked source: `ChapterSirkGroupTransfer.lean` lines 54–63.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkGroupTransfer.lean#L54-L63

-- Generated from ChapterSirkGroupTransfer.lean — theorem BookProof.ChapterSirkGroupTransfer.norm_pow_le_of_le
import Mathlib
import Definitions.Def_ChapterSirkGroupTransfer
open BookProof.ChapterSirkGroupTransfer







noncomputable section


open NormedSpace

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in

theorem BookProof.ChapterSirkGroupTransfer.norm_pow_le_of_le {a : A} {M : ℝ} (ha : ‖a‖ ≤ M) (n : ℕ) : ‖a ^ n‖ ≤ M ^ n := by sorry
