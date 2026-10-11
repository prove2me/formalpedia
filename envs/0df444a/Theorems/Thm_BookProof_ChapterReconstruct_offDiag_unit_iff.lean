-- Prove2me | Theorems.Thm_BookProof_ChapterReconstruct_offDiag_unit_iff
-- name    : BookProof.ChapterReconstruct.offDiag_unit_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T22:58:37.672115+00:00
-- url     : https://prove2.me/theorems/5b0a1a5f-83ce-47e4-a042-9051906435c0
-- title:
--   `BookProof.ChapterReconstruct.offDiag_unit_iff` (U : Fin n → Fin n → ℂ) : (∀ (a : Fin n) (Ψ : Fin n → ℂ), (∑ k : Fin n, ‖Ψ k‖ ^ 2) = 1 → offDiag U a Ψ = 0) ↔ IsDeterministic U
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReconstruct`.
--
--   `BookProof.ChapterReconstruct.offDiag_unit_iff` (U : Fin n → Fin n → ℂ) : (∀ (a : Fin n) (Ψ : Fin n → ℂ), (∑ k : Fin n, ‖Ψ k‖ ^ 2) = 1 → offDiag U a Ψ = 0) ↔ IsDeterministic U
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterReconstruct.offDiag_unit_iff`.

-- Generated from ChapterReconstruct.lean — theorem BookProof.ChapterReconstruct.offDiag_unit_iff
import Mathlib
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterReconstruct.offDiag_unit_iff (U : Fin n → Fin n → ℂ) :
    (∀ (a : Fin n) (Ψ : Fin n → ℂ), (∑ k : Fin n, ‖Ψ k‖ ^ 2) = 1 →
        offDiag U a Ψ = 0) ↔ IsDeterministic U := by sorry
