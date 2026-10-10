-- Prove2me | Theorems.Thm_BookProof_ChapterReconstruct_offDiag_eq_zero_iff_isDeterministic
-- name    : BookProof.ChapterReconstruct.offDiag_eq_zero_iff_isDeterministic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:03:01.658982+00:00
-- url     : https://prove2.me/theorems/02594f3f-3b35-4c49-b9a5-b5499ffc076a
-- title:
--   `BookProof.ChapterReconstruct.offDiag_eq_zero_iff_isDeterministic` (U : Fin n → Fin n → ℂ) : (∀ (a : Fin n) (Ψ : Fin n → ℂ), offDiag U a Ψ = 0) ↔ IsDeterministic U
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReconstruct`.
--
--   `BookProof.ChapterReconstruct.offDiag_eq_zero_iff_isDeterministic` (U : Fin n → Fin n → ℂ) : (∀ (a : Fin n) (Ψ : Fin n → ℂ), offDiag U a Ψ = 0) ↔ IsDeterministic U
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterReconstruct.offDiag_eq_zero_iff_isDeterministic`.

-- Generated from ChapterReconstruct.lean — theorem BookProof.ChapterReconstruct.offDiag_eq_zero_iff_isDeterministic
import Mathlib
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterReconstruct.offDiag_eq_zero_iff_isDeterministic (U : Fin n → Fin n → ℂ) :
    (∀ (a : Fin n) (Ψ : Fin n → ℂ), offDiag U a Ψ = 0) ↔ IsDeterministic U := by sorry
