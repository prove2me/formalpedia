-- Prove2me | Theorems.Thm_BookProof_SymmetryEntropy_entropy_eq_zero_iff
-- name    : BookProof.SymmetryEntropy.entropy_eq_zero_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:02:24.091071+00:00
-- url     : https://prove2.me/theorems/cf9268fb-22a3-4e04-9b2c-063b7ff934b2
-- title:
--   `BookProof.SymmetryEntropy.entropy_eq_zero_iff` {p : Fin n → ℝ} (h0 : ∀ k, 0 ≤ p k) (h1 : ∀ k, p k ≤ 1) : entropy p = 0 ↔ ∀ k, p k = 0 ∨ p k = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSymmetryEntropy`.
--
--   `BookProof.SymmetryEntropy.entropy_eq_zero_iff` {p : Fin n → ℝ} (h0 : ∀ k, 0 ≤ p k) (h1 : ∀ k, p k ≤ 1) : entropy p = 0 ↔ ∀ k, p k = 0 ∨ p k = 1
--
--   Formalization note: Lean 4 identifier `BookProof.SymmetryEntropy.entropy_eq_zero_iff`.

-- Generated from ChapterSymmetryEntropy.lean — theorem BookProof.SymmetryEntropy.entropy_eq_zero_iff
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterReconstruct
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
import Definitions.Def_ChapterIrreversible
open BookProof.SymmetryEntropy



open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

theorem BookProof.SymmetryEntropy.entropy_eq_zero_iff {p : Fin n → ℝ} (h0 : ∀ k, 0 ≤ p k) (h1 : ∀ k, p k ≤ 1) :
    entropy p = 0 ↔ ∀ k, p k = 0 ∨ p k = 1 := by sorry
