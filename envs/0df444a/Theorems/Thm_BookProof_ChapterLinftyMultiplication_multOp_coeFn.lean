-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_coeFn
-- name    : BookProof.ChapterLinftyMultiplication.multOp_coeFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T09:32:21.261982+00:00
-- url     : https://prove2.me/theorems/bb8632c5-1081-4243-b83d-8d09645aa053
-- title:
--   `BookProof.ChapterLinftyMultiplication.multOp_coeFn` (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) (f : Lp ℂ 2 μ) : (multOp φ hφ f : α → ℂ) =ᵐ[μ] fun x => φ x * (f : α → ℂ) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMultiplication`.
--
--   `BookProof.ChapterLinftyMultiplication.multOp_coeFn` (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) (f : Lp ℂ 2 μ) : (multOp φ hφ f : α → ℂ) =ᵐ[μ] fun x => φ x * (f : α → ℂ) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMultiplication.multOp_coeFn`.

-- Generated from ChapterLinftyMultiplication.lean — theorem BookProof.ChapterLinftyMultiplication.multOp_coeFn
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication


noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterLinftyMultiplication.multOp_coeFn (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) (f : Lp ℂ 2 μ) :
    (multOp φ hφ f : α → ℂ) =ᵐ[μ] fun x => φ x * (f : α → ℂ) x := by sorry
