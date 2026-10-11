-- Prove2me | Theorems.Thm_BookProof_ChapterReconstruct_offDiag_eq
-- name    : BookProof.ChapterReconstruct.offDiag_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T22:57:55.277846+00:00
-- url     : https://prove2.me/theorems/8cb1368c-071f-4742-a285-78b96c85e101
-- title:
--   `BookProof.ChapterReconstruct.offDiag_eq` (U : Fin n → Fin n → ℂ) (a : Fin n) (Ψ : Fin n → ℂ) : offDiag U a Ψ = (∑ k : Fin n, (starRingEnd ℂ) (U k a) * Ψ k) * (∑ b : Fin n, (starRi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReconstruct`.
--
--   `BookProof.ChapterReconstruct.offDiag_eq` (U : Fin n → Fin n → ℂ) (a : Fin n) (Ψ : Fin n → ℂ) : offDiag U a Ψ = (∑ k : Fin n, (starRingEnd ℂ) (U k a) * Ψ k) * (∑ b : Fin n, (starRingEnd ℂ) (Ψ b) * U b a) - ∑ k : Fin n, (starRingEnd ℂ) (U k a) * Ψ k * (starRingEnd ℂ) (Ψ k) * U k a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterReconstruct.offDiag_eq`.

-- Generated from ChapterReconstruct.lean — theorem BookProof.ChapterReconstruct.offDiag_eq
import Mathlib
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterReconstruct.offDiag_eq (U : Fin n → Fin n → ℂ) (a : Fin n) (Ψ : Fin n → ℂ) :
    offDiag U a Ψ =
      (∑ k : Fin n, (starRingEnd ℂ) (U k a) * Ψ k) *
        (∑ b : Fin n, (starRingEnd ℂ) (Ψ b) * U b a) -
      ∑ k : Fin n,
        (starRingEnd ℂ) (U k a) * Ψ k * (starRingEnd ℂ) (Ψ k) * U k a := by sorry
