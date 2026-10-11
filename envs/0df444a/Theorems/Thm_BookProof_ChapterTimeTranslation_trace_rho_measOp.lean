-- Prove2me | Theorems.Thm_BookProof_ChapterTimeTranslation_trace_rho_measOp
-- name    : BookProof.ChapterTimeTranslation.trace_rho_measOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:25:16.491247+00:00
-- url     : https://prove2.me/theorems/a4b02361-c1a5-4e7a-9164-92e983463493
-- title:
--   `BookProof.ChapterTimeTranslation.trace_rho_measOp` (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (Ψ : Fin n → ℂ) : (rho Ψ * measOp U a).trace = (∑ k : Fin n, (starRingEnd ℂ) (U k a)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTimeTranslation`.
--
--   `BookProof.ChapterTimeTranslation.trace_rho_measOp` (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (Ψ : Fin n → ℂ) : (rho Ψ * measOp U a).trace = (∑ k : Fin n, (starRingEnd ℂ) (U k a) * Ψ k) * (∑ b : Fin n, (starRingEnd ℂ) (Ψ b) * U b a)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTimeTranslation.trace_rho_measOp`.

-- Generated from ChapterTimeTranslation.lean — theorem BookProof.ChapterTimeTranslation.trace_rho_measOp
import Definitions.Def_ChapterReconstruct
import Mathlib
import Definitions.Def_ChapterTimeTranslation
open BookProof.ChapterTimeTranslation


open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}

theorem BookProof.ChapterTimeTranslation.trace_rho_measOp (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (Ψ : Fin n → ℂ) :
    (rho Ψ * measOp U a).trace =
      (∑ k : Fin n, (starRingEnd ℂ) (U k a) * Ψ k) *
        (∑ b : Fin n, (starRingEnd ℂ) (Ψ b) * U b a) := by sorry
