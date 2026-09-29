-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGroupTransfer_norm_pow_sub_pow_le
-- name    : BookProof.ChapterSirkGroupTransfer.norm_pow_sub_pow_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T05:49:50.633161+00:00
-- url     : https://prove2.me/theorems/1efced88-f3fb-4878-8118-9705010de53b
-- title:
--   The telescoping estimate.** `Aⁿ − Bⁿ = A(Aⁿ⁻¹ − Bⁿ⁻¹) + (A − B)Bⁿ⁻¹` iterated: on the ball of radius `M` the `n`-th power map is Lipschitz with constant `n M^{n−1}`
-- statement:
--   **The telescoping estimate.**  `Aⁿ − Bⁿ = A(Aⁿ⁻¹ − Bⁿ⁻¹) + (A − B)Bⁿ⁻¹`
--   iterated: on the ball of radius `M` the `n`-th power map is Lipschitz with
--   constant `n M^{n−1}`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterSirkGroupTransfer.norm_pow_sub_pow_le` (module `BookProof.SirkGroupTransfer`), line-linked source: `ChapterSirkGroupTransfer.lean` lines 65–91.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkGroupTransfer.lean#L65-L91

-- Generated from ChapterSirkGroupTransfer.lean — theorem BookProof.ChapterSirkGroupTransfer.norm_pow_sub_pow_le
import Mathlib
import Definitions.Def_ChapterSirkGroupTransfer
open BookProof.ChapterSirkGroupTransfer







noncomputable section


open NormedSpace

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in

theorem BookProof.ChapterSirkGroupTransfer.norm_pow_sub_pow_le {a b : A} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1) * M ^ n * ‖a - b‖ := by sorry
