-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGroupTransfer_norm_exp_sub_exp_le
-- name    : BookProof.ChapterSirkGroupTransfer.norm_exp_sub_exp_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:10:31.541708+00:00
-- url     : https://prove2.me/theorems/273fe1c3-4d47-4bda-ac72-98bb554d5a51
-- title:
--   `‖exp a − exp b‖ ≤ ‖a − b‖ e^{M}`** for `‖a‖, ‖b‖ ≤ M`: summing the telescoping estimate against the exponential series
-- statement:
--   **`‖exp a − exp b‖ ≤ ‖a − b‖ e^{M}`** for `‖a‖, ‖b‖ ≤ M`: summing the
--   telescoping estimate against the exponential series.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterSirkGroupTransfer.norm_exp_sub_exp_le` (module `BookProof.SirkGroupTransfer`), line-linked source: `ChapterSirkGroupTransfer.lean` lines 95–146.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkGroupTransfer.lean#L95-L146

-- Generated from ChapterSirkGroupTransfer.lean — theorem BookProof.ChapterSirkGroupTransfer.norm_exp_sub_exp_le
import Mathlib
import Definitions.Def_ChapterSirkGroupTransfer
open BookProof.ChapterSirkGroupTransfer







noncomputable section


open NormedSpace

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem BookProof.ChapterSirkGroupTransfer.norm_exp_sub_exp_le {a b : A} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖exp a - exp b‖ ≤ ‖a - b‖ * Real.exp M := by sorry
