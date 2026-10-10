-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_eq_zero_iff
-- name    : BookProof.ChapterLinftyMultiplication.multOp_eq_zero_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:31:25.064488+00:00
-- url     : https://prove2.me/theorems/0fee0b32-d89a-448d-9614-555b6d35fdf5
-- title:
--   `BookProof.ChapterLinftyMultiplication.multOp_eq_zero_iff` [IsFiniteMeasure μ] (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) : multOp φ hφ = 0 ↔ φ =ᵐ[μ] 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMultiplication`.
--
--   `BookProof.ChapterLinftyMultiplication.multOp_eq_zero_iff` [IsFiniteMeasure μ] (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) : multOp φ hφ = 0 ↔ φ =ᵐ[μ] 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMultiplication.multOp_eq_zero_iff`.

-- Generated from ChapterLinftyMultiplication.lean — theorem BookProof.ChapterLinftyMultiplication.multOp_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication


noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterLinftyMultiplication.multOp_eq_zero_iff [IsFiniteMeasure μ] (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) :
    multOp φ hφ = 0 ↔ φ =ᵐ[μ] 0 := by sorry
