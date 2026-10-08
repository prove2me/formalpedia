-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMultiplication_memLp_top_conj
-- name    : BookProof.ChapterLinftyMultiplication.memLp_top_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:12:12.231676+00:00
-- url     : https://prove2.me/theorems/62aa62ab-9468-4e2e-afa3-15426872f554
-- title:
--   `BookProof.ChapterLinftyMultiplication.memLp_top_conj` {φ : α → ℂ} (hφ : MemLp φ ⊤ μ) : MemLp (fun x => (starRingEnd ℂ) (φ x)) ⊤ μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMultiplication`.
--
--   `BookProof.ChapterLinftyMultiplication.memLp_top_conj` {φ : α → ℂ} (hφ : MemLp φ ⊤ μ) : MemLp (fun x => (starRingEnd ℂ) (φ x)) ⊤ μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMultiplication.memLp_top_conj`.

-- Generated from ChapterLinftyMultiplication.lean — theorem BookProof.ChapterLinftyMultiplication.memLp_top_conj
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication


noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterLinftyMultiplication.memLp_top_conj {φ : α → ℂ} (hφ : MemLp φ ⊤ μ) :
    MemLp (fun x => (starRingEnd ℂ) (φ x)) ⊤ μ := by sorry
