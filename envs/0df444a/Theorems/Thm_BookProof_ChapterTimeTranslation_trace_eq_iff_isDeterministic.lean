-- Prove2me | Theorems.Thm_BookProof_ChapterTimeTranslation_trace_eq_iff_isDeterministic
-- name    : BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:25:53.763977+00:00
-- url     : https://prove2.me/theorems/dc19c4f2-8c73-4c74-8a12-41a169085064
-- title:
--   `BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic` (U : Matrix (Fin n) (Fin n) ℂ) : (∀ (a : Fin n) (Ψ : Fin n → ℂ), (diagPart (rho Ψ) * measOp U a).trace = (rho Ψ * me
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTimeTranslation`.
--
--   `BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic` (U : Matrix (Fin n) (Fin n) ℂ) : (∀ (a : Fin n) (Ψ : Fin n → ℂ), (diagPart (rho Ψ) * measOp U a).trace = (rho Ψ * measOp U a).trace) ↔ IsDeterministic U
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic`.

-- Generated from ChapterTimeTranslation.lean — theorem BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic
import Mathlib
import Definitions.Def_ChapterTimeTranslation
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct
open BookProof.ChapterTimeTranslation


open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}

theorem BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic (U : Matrix (Fin n) (Fin n) ℂ) :
    (∀ (a : Fin n) (Ψ : Fin n → ℂ),
        (diagPart (rho Ψ) * measOp U a).trace = (rho Ψ * measOp U a).trace)
      ↔ IsDeterministic U := by sorry
