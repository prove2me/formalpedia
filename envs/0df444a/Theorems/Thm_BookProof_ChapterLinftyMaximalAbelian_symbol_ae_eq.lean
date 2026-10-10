-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_symbol_ae_eq
-- name    : BookProof.ChapterLinftyMaximalAbelian.symbol_ae_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:29:27.863631+00:00
-- url     : https://prove2.me/theorems/428b39cc-18ad-43ab-a91e-7b171b541617
-- title:
--   `BookProof.ChapterLinftyMaximalAbelian.symbol_ae_eq` (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : (T (oneLp μ) : α → ℂ) =ᵐ[μ] symbol T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMaximalAbelian`.
--
--   `BookProof.ChapterLinftyMaximalAbelian.symbol_ae_eq` (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : (T (oneLp μ) : α → ℂ) =ᵐ[μ] symbol T
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMaximalAbelian.symbol_ae_eq`.

-- Generated from ChapterLinftyMaximalAbelian.lean — theorem BookProof.ChapterLinftyMaximalAbelian.symbol_ae_eq
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
open BookProof.ChapterLinftyMaximalAbelian


noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem BookProof.ChapterLinftyMaximalAbelian.symbol_ae_eq (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    (T (oneLp μ) : α → ℂ) =ᵐ[μ] symbol T := by sorry
