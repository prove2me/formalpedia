-- Prove2me | Theorems.Thm_BookProof_ChapterMarkovEntropy_applyMarkov_permMatrix
-- name    : BookProof.ChapterMarkovEntropy.applyMarkov_permMatrix
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:58:00.800168+00:00
-- url     : https://prove2.me/theorems/b8323235-f9aa-48b6-a02d-b7b85ddce0ba
-- title:
--   `BookProof.ChapterMarkovEntropy.applyMarkov_permMatrix` (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) : applyMarkov (permMatrix σ) p = fun j => p (σ.symm j)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMarkovEntropy`.
--
--   `BookProof.ChapterMarkovEntropy.applyMarkov_permMatrix` (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) : applyMarkov (permMatrix σ) p = fun j => p (σ.symm j)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMarkovEntropy.applyMarkov_permMatrix`.

-- Generated from ChapterMarkovEntropy.lean — theorem BookProof.ChapterMarkovEntropy.applyMarkov_permMatrix
import Mathlib
import Definitions.Def_ChapterMarkovEntropy
open BookProof.ChapterMarkovEntropy


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterMarkovEntropy.applyMarkov_permMatrix (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    applyMarkov (permMatrix σ) p = fun j => p (σ.symm j) := by sorry
