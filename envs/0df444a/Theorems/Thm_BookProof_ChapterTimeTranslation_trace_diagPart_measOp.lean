-- Prove2me | Theorems.Thm_BookProof_ChapterTimeTranslation_trace_diagPart_measOp
-- name    : BookProof.ChapterTimeTranslation.trace_diagPart_measOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:25:22.106644+00:00
-- url     : https://prove2.me/theorems/1f13a453-4a5f-4be4-baaf-44ce980c1536
-- title:
--   `BookProof.ChapterTimeTranslation.trace_diagPart_measOp` (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (Ψ : Fin n → ℂ) : (diagPart (rho Ψ) * measOp U a).trace = ∑ k : Fin n, (starRing
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTimeTranslation`.
--
--   `BookProof.ChapterTimeTranslation.trace_diagPart_measOp` (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (Ψ : Fin n → ℂ) : (diagPart (rho Ψ) * measOp U a).trace = ∑ k : Fin n, (starRingEnd ℂ) (U k a) * Ψ k * (starRingEnd ℂ) (Ψ k) * U k a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTimeTranslation.trace_diagPart_measOp`.

-- Generated from ChapterTimeTranslation.lean — theorem BookProof.ChapterTimeTranslation.trace_diagPart_measOp
import Definitions.Def_ChapterReconstruct
import Mathlib
import Definitions.Def_ChapterTimeTranslation
open BookProof.ChapterTimeTranslation


open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}

theorem BookProof.ChapterTimeTranslation.trace_diagPart_measOp (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (Ψ : Fin n → ℂ) :
    (diagPart (rho Ψ) * measOp U a).trace =
      ∑ k : Fin n,
        (starRingEnd ℂ) (U k a) * Ψ k * (starRingEnd ℂ) (Ψ k) * U k a := by sorry
