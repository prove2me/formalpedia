-- Prove2me | Theorems.Thm_BookProof_ChapterReconstruct_isDeterministicCol_of_offDiag
-- name    : BookProof.ChapterReconstruct.isDeterministicCol_of_offDiag
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:02:52.26598+00:00
-- url     : https://prove2.me/theorems/d1f62cbc-c913-44af-a34a-fcebc6b88f81
-- title:
--   `BookProof.ChapterReconstruct.isDeterministicCol_of_offDiag` (U : Fin n → Fin n → ℂ) (a : Fin n) (hU : ∀ Ψ : Fin n → ℂ, offDiag U a Ψ = 0) : IsDeterministicCol U a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReconstruct`.
--
--   `BookProof.ChapterReconstruct.isDeterministicCol_of_offDiag` (U : Fin n → Fin n → ℂ) (a : Fin n) (hU : ∀ Ψ : Fin n → ℂ, offDiag U a Ψ = 0) : IsDeterministicCol U a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterReconstruct.isDeterministicCol_of_offDiag`.

-- Generated from ChapterReconstruct.lean — theorem BookProof.ChapterReconstruct.isDeterministicCol_of_offDiag
import Mathlib
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterReconstruct.isDeterministicCol_of_offDiag (U : Fin n → Fin n → ℂ) (a : Fin n)
    (hU : ∀ Ψ : Fin n → ℂ, offDiag U a Ψ = 0) : IsDeterministicCol U a := by sorry
