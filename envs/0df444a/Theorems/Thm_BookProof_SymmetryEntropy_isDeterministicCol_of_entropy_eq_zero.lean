-- Prove2me | Theorems.Thm_BookProof_SymmetryEntropy_isDeterministicCol_of_entropy_eq_zero
-- name    : BookProof.SymmetryEntropy.isDeterministicCol_of_entropy_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:03:34.795348+00:00
-- url     : https://prove2.me/theorems/cbca7b87-88ac-4532-b2d7-32f448a693f9
-- title:
--   `BookProof.SymmetryEntropy.isDeterministicCol_of_entropy_eq_zero` {U : Fin n → Fin n → ℂ} {a : Fin n} (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (h : entropy (bornCol U a) = 0) : IsDeterministi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSymmetryEntropy`.
--
--   `BookProof.SymmetryEntropy.isDeterministicCol_of_entropy_eq_zero` {U : Fin n → Fin n → ℂ} {a : Fin n} (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (h : entropy (bornCol U a) = 0) : IsDeterministicCol U a
--
--   Formalization note: Lean 4 identifier `BookProof.SymmetryEntropy.isDeterministicCol_of_entropy_eq_zero`.

-- Generated from ChapterSymmetryEntropy.lean — theorem BookProof.SymmetryEntropy.isDeterministicCol_of_entropy_eq_zero
import Definitions.Def_ChapterMarkovEntropy
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
import Definitions.Def_ChapterIrreversible
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct
open BookProof.SymmetryEntropy



open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

theorem BookProof.SymmetryEntropy.isDeterministicCol_of_entropy_eq_zero {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (h : entropy (bornCol U a) = 0) :
    IsDeterministicCol U a := by sorry
