-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGroupTransfer_groupFlow_transfer_uniform_on_interval
-- name    : BookProof.ChapterSirkGroupTransfer.groupFlow_transfer_uniform_on_interval
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:14:45.086726+00:00
-- url     : https://prove2.me/theorems/9e6f40c3-b2be-4eaf-80fa-8c1ebafefbf9
-- title:
--   Uniformity on compact time intervals.** On `[−T, T]` the two propagators differ by at most `T ‖a − b‖ e^{T M}`, a bound independent of `t`: generator convergence in norm gives convergence
-- statement:
--   **Uniformity on compact time intervals.**  On `[−T, T]` the two propagators
--   differ by at most `T ‖a − b‖ e^{T M}`, a bound independent of `t`: generator
--   convergence in norm gives convergence of the flows uniformly in time on every
--   bounded interval.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterSirkGroupTransfer.groupFlow_transfer_uniform_on_interval` (module `BookProof.SirkGroupTransfer`), line-linked source: `ChapterSirkGroupTransfer.lean` lines 178–187.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkGroupTransfer.lean#L178-L187

-- Generated from ChapterSirkGroupTransfer.lean — theorem BookProof.ChapterSirkGroupTransfer.groupFlow_transfer_uniform_on_interval
import Mathlib
import Definitions.Def_ChapterSirkGroupTransfer
open BookProof.ChapterSirkGroupTransfer







noncomputable section


open NormedSpace

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem BookProof.ChapterSirkGroupTransfer.groupFlow_transfer_uniform_on_interval {a b : A} {M T : ℝ} (ha : ‖a‖ ≤ M)
    (hb : ‖b‖ ≤ M) (hT : 0 ≤ T) {t : ℝ} (ht : |t| ≤ T) :
    ‖groupFlow a t - groupFlow b t‖ ≤ T * ‖a - b‖ * Real.exp (T * M) := by sorry
