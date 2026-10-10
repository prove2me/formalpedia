-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_symbol_mul
-- name    : BookProof.ChapterLinftyMaximalAbelian.symbol_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:29:44.215103+00:00
-- url     : https://prove2.me/theorems/2d27d7ca-9082-41ec-a46f-15068407210a
-- title:
--   `BookProof.ChapterLinftyMaximalAbelian.symbol_mul` {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) : ((T (multOp φ hφ (oneLp μ)))...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMaximalAbelian`.
--
--   `BookProof.ChapterLinftyMaximalAbelian.symbol_mul` {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) : ((T (multOp φ hφ (oneLp μ))) : α → ℂ) =ᵐ[μ] fun x => φ x * symbol T x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMaximalAbelian.symbol_mul`.

-- Generated from ChapterLinftyMaximalAbelian.lean — theorem BookProof.ChapterLinftyMaximalAbelian.symbol_mul
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLinftyMaximalAbelian


noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem BookProof.ChapterLinftyMaximalAbelian.symbol_mul {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T)
    (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) :
    ((T (multOp φ hφ (oneLp μ))) : α → ℂ) =ᵐ[μ] fun x => φ x * symbol T x := by sorry
