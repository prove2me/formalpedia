-- Prove2me | Theorems.Thm_BookProof_ChapterReconstruct_offDiag_of_isDeterministicCol
-- name    : BookProof.ChapterReconstruct.offDiag_of_isDeterministicCol
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T22:57:59.485979+00:00
-- url     : https://prove2.me/theorems/82b98293-10ea-4658-985d-0861cea715f8
-- title:
--   `BookProof.ChapterReconstruct.offDiag_of_isDeterministicCol` (U : Fin n → Fin n → ℂ) (a : Fin n) (hU : IsDeterministicCol U a) (Ψ : Fin n → ℂ) : offDiag U a Ψ = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReconstruct`.
--
--   `BookProof.ChapterReconstruct.offDiag_of_isDeterministicCol` (U : Fin n → Fin n → ℂ) (a : Fin n) (hU : IsDeterministicCol U a) (Ψ : Fin n → ℂ) : offDiag U a Ψ = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterReconstruct.offDiag_of_isDeterministicCol`.

-- Generated from ChapterReconstruct.lean — theorem BookProof.ChapterReconstruct.offDiag_of_isDeterministicCol
import Mathlib
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterReconstruct.offDiag_of_isDeterministicCol (U : Fin n → Fin n → ℂ) (a : Fin n)
    (hU : IsDeterministicCol U a) (Ψ : Fin n → ℂ) : offDiag U a Ψ = 0 := by sorry
