-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_symbol_ae_norm_le
-- name    : BookProof.ChapterLinftyMaximalAbelian.symbol_ae_norm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:29:42.107601+00:00
-- url     : https://prove2.me/theorems/c28799e4-87aa-4c62-94c5-e75fad36a531
-- title:
--   `BookProof.ChapterLinftyMaximalAbelian.symbol_ae_norm_le` {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) : ∀ᵐ x ∂μ, ‖symbol T x‖ ≤ ‖T‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMaximalAbelian`.
--
--   `BookProof.ChapterLinftyMaximalAbelian.symbol_ae_norm_le` {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) : ∀ᵐ x ∂μ, ‖symbol T x‖ ≤ ‖T‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMaximalAbelian.symbol_ae_norm_le`.

-- Generated from ChapterLinftyMaximalAbelian.lean — theorem BookProof.ChapterLinftyMaximalAbelian.symbol_ae_norm_le
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLinftyMaximalAbelian


noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem BookProof.ChapterLinftyMaximalAbelian.symbol_ae_norm_le {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) :
    ∀ᵐ x ∂μ, ‖symbol T x‖ ≤ ‖T‖ := by sorry
