-- Prove2me | Theorems.Thm_BookProof_ChapterTimeTranslation_trace_diff
-- name    : BookProof.ChapterTimeTranslation.trace_diff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:25:37.872825+00:00
-- url     : https://prove2.me/theorems/3b08b305-3106-4018-b9e3-aae7f6252958
-- title:
--   `BookProof.ChapterTimeTranslation.trace_diff` (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (Ψ : Fin n → ℂ) : (rho Ψ * measOp U a).trace - (diagPart (rho Ψ) * measOp U a).trace = offD
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTimeTranslation`.
--
--   `BookProof.ChapterTimeTranslation.trace_diff` (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (Ψ : Fin n → ℂ) : (rho Ψ * measOp U a).trace - (diagPart (rho Ψ) * measOp U a).trace = offDiag U a Ψ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTimeTranslation.trace_diff`.

-- Generated from ChapterTimeTranslation.lean — theorem BookProof.ChapterTimeTranslation.trace_diff
import Mathlib
import Definitions.Def_ChapterTimeTranslation
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct
open BookProof.ChapterTimeTranslation


open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}

theorem BookProof.ChapterTimeTranslation.trace_diff (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (Ψ : Fin n → ℂ) :
    (rho Ψ * measOp U a).trace - (diagPart (rho Ψ) * measOp U a).trace
      = offDiag U a Ψ := by sorry
