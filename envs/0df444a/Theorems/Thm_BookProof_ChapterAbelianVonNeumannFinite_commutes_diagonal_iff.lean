-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianVonNeumannFinite_commutes_diagonal_iff
-- name    : BookProof.ChapterAbelianVonNeumannFinite.commutes_diagonal_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:51:20.985612+00:00
-- url     : https://prove2.me/theorems/016e527e-1a0f-49a8-89db-a06a0b6c1c31
-- title:
--   `BookProof.ChapterAbelianVonNeumannFinite.commutes_diagonal_iff` (e : n → ℂ) (he : Function.Injective e) (M : Matrix n n ℂ) : M * diagonal e = diagonal e * M ↔ ∃ d : n → ℂ, M = dia
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianVonNeumannFinite`.
--
--   `BookProof.ChapterAbelianVonNeumannFinite.commutes_diagonal_iff` (e : n → ℂ) (he : Function.Injective e) (M : Matrix n n ℂ) : M * diagonal e = diagonal e * M ↔ ∃ d : n → ℂ, M = diagonal d
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianVonNeumannFinite.commutes_diagonal_iff`.

-- Generated from ChapterAbelianVonNeumannFinite.lean — theorem BookProof.ChapterAbelianVonNeumannFinite.commutes_diagonal_iff
import Mathlib
import Definitions.Def_ChapterAbelianVonNeumannFinite
open BookProof.ChapterAbelianVonNeumannFinite


open Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterAbelianVonNeumannFinite.commutes_diagonal_iff (e : n → ℂ) (he : Function.Injective e) (M : Matrix n n ℂ) :
    M * diagonal e = diagonal e * M ↔ ∃ d : n → ℂ, M = diagonal d := by sorry
