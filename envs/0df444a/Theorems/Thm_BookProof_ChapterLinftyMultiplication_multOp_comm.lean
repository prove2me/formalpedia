-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_comm
-- name    : BookProof.ChapterLinftyMultiplication.multOp_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:31:01.192982+00:00
-- url     : https://prove2.me/theorems/04d73c31-924f-436b-a0a7-622445e5a50e
-- title:
--   `BookProof.ChapterLinftyMultiplication.multOp_comm` (φ ψ : α → ℂ) (hφ : MemLp φ ⊤ μ) (hψ : MemLp ψ ⊤ μ) : (multOp φ hφ).comp (multOp ψ hψ) = (multOp ψ hψ).comp (multOp φ hφ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMultiplication`.
--
--   `BookProof.ChapterLinftyMultiplication.multOp_comm` (φ ψ : α → ℂ) (hφ : MemLp φ ⊤ μ) (hψ : MemLp ψ ⊤ μ) : (multOp φ hφ).comp (multOp ψ hψ) = (multOp ψ hψ).comp (multOp φ hφ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMultiplication.multOp_comm`.

-- Generated from ChapterLinftyMultiplication.lean — theorem BookProof.ChapterLinftyMultiplication.multOp_comm
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication


noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterLinftyMultiplication.multOp_comm (φ ψ : α → ℂ) (hφ : MemLp φ ⊤ μ) (hψ : MemLp ψ ⊤ μ) :
    (multOp φ hφ).comp (multOp ψ hψ) = (multOp ψ hψ).comp (multOp φ hφ) := by sorry
