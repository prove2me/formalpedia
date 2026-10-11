-- Prove2me | Theorems.Thm_BookProof_ChapterTimeTranslation_trace_eq_iff_isDeterministic_pure
-- name    : BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic_pure
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:26:02.760024+00:00
-- url     : https://prove2.me/theorems/d22c684a-dd88-4b49-8205-a6820b8d783e
-- title:
--   `BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic_pure` (U : Matrix (Fin n) (Fin n) ℂ) : (∀ (a : Fin n) (Ψ : Fin n → ℂ), (∑ k : Fin n, ‖Ψ k‖ ^ 2) = 1 → (diagPart (rho
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTimeTranslation`.
--
--   `BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic_pure` (U : Matrix (Fin n) (Fin n) ℂ) : (∀ (a : Fin n) (Ψ : Fin n → ℂ), (∑ k : Fin n, ‖Ψ k‖ ^ 2) = 1 → (diagPart (rho Ψ) * measOp U a).trace = (rho Ψ * measOp U a).trace) ↔ IsDeterministic U
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic_pure`.

-- Generated from ChapterTimeTranslation.lean — theorem BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic_pure
import Mathlib
import Definitions.Def_ChapterTimeTranslation
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct
open BookProof.ChapterTimeTranslation


open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}

theorem BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic_pure (U : Matrix (Fin n) (Fin n) ℂ) :
    (∀ (a : Fin n) (Ψ : Fin n → ℂ), (∑ k : Fin n, ‖Ψ k‖ ^ 2) = 1 →
        (diagPart (rho Ψ) * measOp U a).trace = (rho Ψ * measOp U a).trace)
      ↔ IsDeterministic U := by sorry
