-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGroupTransfer_norm_groupFlow_sub_le
-- name    : BookProof.ChapterSirkGroupTransfer.norm_groupFlow_sub_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:13:43.826714+00:00
-- url     : https://prove2.me/theorems/86210964-62f0-4b3f-9b51-33473e7d48b1
-- title:
--   The unitary-group transfer for bounded generators (§12.2 Gap 3, the bounded half).** Two bounded generators of norm at most `M` produce propagators that differ by at most `|t| ‖a − b‖ e^{|
-- statement:
--   **The unitary-group transfer for bounded generators (§12.2 Gap 3, the
--   bounded half).**  Two bounded generators of norm at most `M` produce propagators
--   that differ by at most `|t| ‖a − b‖ e^{|t| M}` at time `t`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterSirkGroupTransfer.norm_groupFlow_sub_le` (module `BookProof.SirkGroupTransfer`), line-linked source: `ChapterSirkGroupTransfer.lean` lines 157–176.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkGroupTransfer.lean#L157-L176

-- Generated from ChapterSirkGroupTransfer.lean — theorem BookProof.ChapterSirkGroupTransfer.norm_groupFlow_sub_le
import Mathlib
import Definitions.Def_ChapterSirkGroupTransfer
open BookProof.ChapterSirkGroupTransfer







noncomputable section


open NormedSpace

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem BookProof.ChapterSirkGroupTransfer.norm_groupFlow_sub_le {a b : A} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (t : ℝ) :
    ‖groupFlow a t - groupFlow b t‖ ≤ |t| * ‖a - b‖ * Real.exp (|t| * M) := by sorry
