-- Prove2me | Theorems.Thm_BookProof_ChapterMarkovEntropy_entropy_applyMarkov_permMatrix
-- name    : BookProof.ChapterMarkovEntropy.entropy_applyMarkov_permMatrix
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:01:13.771437+00:00
-- url     : https://prove2.me/theorems/ccac01f7-1f9f-44f7-8f35-c46dd3c1d087
-- title:
--   `BookProof.ChapterMarkovEntropy.entropy_applyMarkov_permMatrix` (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) : entropy (applyMarkov (permMatrix σ) p) = entropy p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMarkovEntropy`.
--
--   `BookProof.ChapterMarkovEntropy.entropy_applyMarkov_permMatrix` (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) : entropy (applyMarkov (permMatrix σ) p) = entropy p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMarkovEntropy.entropy_applyMarkov_permMatrix`.

-- Generated from ChapterMarkovEntropy.lean — theorem BookProof.ChapterMarkovEntropy.entropy_applyMarkov_permMatrix
import Mathlib
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible
open BookProof.ChapterMarkovEntropy


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterMarkovEntropy.entropy_applyMarkov_permMatrix (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    entropy (applyMarkov (permMatrix σ) p) = entropy p := by sorry
