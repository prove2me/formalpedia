-- Prove2me | Theorems.Thm_BookProof_ChapterReconstruct_offDiag_eq_zero_iff
-- name    : BookProof.ChapterReconstruct.offDiag_eq_zero_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:02:59.006731+00:00
-- url     : https://prove2.me/theorems/41a3be0b-541b-442d-8fe2-5394661dadde
-- title:
--   `BookProof.ChapterReconstruct.offDiag_eq_zero_iff` (U : Fin n → Fin n → ℂ) (a : Fin n) : (∀ Ψ : Fin n → ℂ, offDiag U a Ψ = 0) ↔ IsDeterministicCol U a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReconstruct`.
--
--   `BookProof.ChapterReconstruct.offDiag_eq_zero_iff` (U : Fin n → Fin n → ℂ) (a : Fin n) : (∀ Ψ : Fin n → ℂ, offDiag U a Ψ = 0) ↔ IsDeterministicCol U a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterReconstruct.offDiag_eq_zero_iff`.

-- Generated from ChapterReconstruct.lean — theorem BookProof.ChapterReconstruct.offDiag_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterReconstruct.offDiag_eq_zero_iff (U : Fin n → Fin n → ℂ) (a : Fin n) :
    (∀ Ψ : Fin n → ℂ, offDiag U a Ψ = 0) ↔ IsDeterministicCol U a := by sorry
