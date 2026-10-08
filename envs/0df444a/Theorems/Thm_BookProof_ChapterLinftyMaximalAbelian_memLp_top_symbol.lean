-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_memLp_top_symbol
-- name    : BookProof.ChapterLinftyMaximalAbelian.memLp_top_symbol
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:11:55.480978+00:00
-- url     : https://prove2.me/theorems/fa59dff9-37ac-45fa-868f-cd23be344dd8
-- title:
--   `BookProof.ChapterLinftyMaximalAbelian.memLp_top_symbol` {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) : MemLp (symbol T) ⊤ μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMaximalAbelian`.
--
--   `BookProof.ChapterLinftyMaximalAbelian.memLp_top_symbol` {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) : MemLp (symbol T) ⊤ μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMaximalAbelian.memLp_top_symbol`.

-- Generated from ChapterLinftyMaximalAbelian.lean — theorem BookProof.ChapterLinftyMaximalAbelian.memLp_top_symbol
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
open BookProof.ChapterLinftyMaximalAbelian


noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem BookProof.ChapterLinftyMaximalAbelian.memLp_top_symbol {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) :
    MemLp (symbol T) ⊤ μ := by sorry
