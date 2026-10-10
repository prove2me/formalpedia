-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_mul
-- name    : BookProof.ChapterLinftyMultiplication.multOp_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:30:50.754798+00:00
-- url     : https://prove2.me/theorems/43ade2be-f0cc-49dd-aed8-a57e054a3969
-- title:
--   `BookProof.ChapterLinftyMultiplication.multOp_mul` (φ ψ : α → ℂ) (hφ : MemLp φ ⊤ μ) (hψ : MemLp ψ ⊤ μ) : (multOp φ hφ).comp (multOp ψ hψ) = multOp (fun x => φ x * ψ x)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMultiplication`.
--
--   `BookProof.ChapterLinftyMultiplication.multOp_mul` (φ ψ : α → ℂ) (hφ : MemLp φ ⊤ μ) (hψ : MemLp ψ ⊤ μ) : (multOp φ hφ).comp (multOp ψ hψ) = multOp (fun x => φ x * ψ x) (memLp_top_mul hφ hψ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMultiplication.multOp_mul`.

-- Generated from ChapterLinftyMultiplication.lean — theorem BookProof.ChapterLinftyMultiplication.multOp_mul
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_memLp_top_mul
open BookProof.ChapterLinftyMultiplication


noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterLinftyMultiplication.multOp_mul (φ ψ : α → ℂ) (hφ : MemLp φ ⊤ μ) (hψ : MemLp ψ ⊤ μ) :
    (multOp φ hφ).comp (multOp ψ hψ) = multOp (fun x => φ x * ψ x) (memLp_top_mul hφ hψ) := by sorry
