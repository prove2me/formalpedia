-- Prove2me | Theorems.Thm_BookProof_SymmetryEntropy_exists_eq_one_of_isDeterministicCol
-- name    : BookProof.SymmetryEntropy.exists_eq_one_of_isDeterministicCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:02:56.436863+00:00
-- url     : https://prove2.me/theorems/8adf1fd6-5350-40c5-a475-2433ca0f1659
-- title:
--   `BookProof.SymmetryEntropy.exists_eq_one_of_isDeterministicCol` {U : Fin n → Fin n → ℂ} {a : Fin n} (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (hdet : IsDeterministicCol U a) : ∃ k, bornCol U a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSymmetryEntropy`.
--
--   `BookProof.SymmetryEntropy.exists_eq_one_of_isDeterministicCol` {U : Fin n → Fin n → ℂ} {a : Fin n} (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (hdet : IsDeterministicCol U a) : ∃ k, bornCol U a k = 1 ∧ ∀ l, l ≠ k → bornCol U a l = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SymmetryEntropy.exists_eq_one_of_isDeterministicCol`.

-- Generated from ChapterSymmetryEntropy.lean — theorem BookProof.SymmetryEntropy.exists_eq_one_of_isDeterministicCol
import Definitions.Def_ChapterMarkovEntropy
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct
open BookProof.SymmetryEntropy



open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

theorem BookProof.SymmetryEntropy.exists_eq_one_of_isDeterministicCol {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (hdet : IsDeterministicCol U a) :
    ∃ k, bornCol U a k = 1 ∧ ∀ l, l ≠ k → bornCol U a l = 0 := by sorry
