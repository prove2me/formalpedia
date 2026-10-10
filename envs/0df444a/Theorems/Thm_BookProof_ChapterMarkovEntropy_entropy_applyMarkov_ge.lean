-- Prove2me | Theorems.Thm_BookProof_ChapterMarkovEntropy_entropy_applyMarkov_ge
-- name    : BookProof.ChapterMarkovEntropy.entropy_applyMarkov_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:57:52.774014+00:00
-- url     : https://prove2.me/theorems/c6204dbe-3c93-4b4a-9ff5-8a74b6252c3b
-- title:
--   `BookProof.ChapterMarkovEntropy.entropy_applyMarkov_ge` (M : Fin n → Fin n → ℝ) (hM : IsDoublyStochastic M) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) : entropy p ≤ entropy (applyMarkov M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMarkovEntropy`.
--
--   `BookProof.ChapterMarkovEntropy.entropy_applyMarkov_ge` (M : Fin n → Fin n → ℝ) (hM : IsDoublyStochastic M) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) : entropy p ≤ entropy (applyMarkov M p)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMarkovEntropy.entropy_applyMarkov_ge`.

-- Generated from ChapterMarkovEntropy.lean — theorem BookProof.ChapterMarkovEntropy.entropy_applyMarkov_ge
import Mathlib
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible
open BookProof.ChapterMarkovEntropy


open scoped BigOperators
open Finset


variable {n : ℕ}

theorem BookProof.ChapterMarkovEntropy.entropy_applyMarkov_ge (M : Fin n → Fin n → ℝ) (hM : IsDoublyStochastic M)
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    entropy p ≤ entropy (applyMarkov M p) := by sorry
