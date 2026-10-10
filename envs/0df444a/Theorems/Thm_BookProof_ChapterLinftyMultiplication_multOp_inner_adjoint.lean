-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_inner_adjoint
-- name    : BookProof.ChapterLinftyMultiplication.multOp_inner_adjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:30:49.99971+00:00
-- url     : https://prove2.me/theorems/7e1efeae-76f2-4a14-a0b3-366852927e35
-- title:
--   `BookProof.ChapterLinftyMultiplication.multOp_inner_adjoint` (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) (f g : Lp ℂ 2 μ) : inner ℂ (multOp φ hφ f) g = inner ℂ f (multOp (fun x => (starRingEnd
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMultiplication`.
--
--   `BookProof.ChapterLinftyMultiplication.multOp_inner_adjoint` (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) (f g : Lp ℂ 2 μ) : inner ℂ (multOp φ hφ f) g = inner ℂ f (multOp (fun x => (starRingEnd ℂ) (φ x)) (memLp_top_conj hφ) g)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMultiplication.multOp_inner_adjoint`.

-- Generated from ChapterLinftyMultiplication.lean — theorem BookProof.ChapterLinftyMultiplication.multOp_inner_adjoint
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_memLp_top_conj
open BookProof.ChapterLinftyMultiplication


noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterLinftyMultiplication.multOp_inner_adjoint (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) (f g : Lp ℂ 2 μ) :
    inner ℂ (multOp φ hφ f) g
      = inner ℂ f (multOp (fun x => (starRingEnd ℂ) (φ x)) (memLp_top_conj hφ) g) := by sorry
