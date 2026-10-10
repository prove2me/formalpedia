-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMultiplication_norm_multOp_le
-- name    : BookProof.ChapterLinftyMultiplication.norm_multOp_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:30:31.50698+00:00
-- url     : https://prove2.me/theorems/d22c6958-2f93-42fa-a3de-d8bc3c955a25
-- title:
--   `BookProof.ChapterLinftyMultiplication.norm_multOp_le` (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) : ‖multOp φ hφ‖ ≤ (eLpNorm φ ⊤ μ).toReal
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMultiplication`.
--
--   `BookProof.ChapterLinftyMultiplication.norm_multOp_le` (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) : ‖multOp φ hφ‖ ≤ (eLpNorm φ ⊤ μ).toReal
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMultiplication.norm_multOp_le`.

-- Generated from ChapterLinftyMultiplication.lean — theorem BookProof.ChapterLinftyMultiplication.norm_multOp_le
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication


noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterLinftyMultiplication.norm_multOp_le (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) :
    ‖multOp φ hφ‖ ≤ (eLpNorm φ ⊤ μ).toReal := by sorry
