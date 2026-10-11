-- Prove2me | Theorems.Thm_BookProof_SymmetryEntropy_bornCol_eq_zero_iff
-- name    : BookProof.SymmetryEntropy.bornCol_eq_zero_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:02:43.609989+00:00
-- url     : https://prove2.me/theorems/080aadec-6b0e-4f37-b03e-3020604e180f
-- title:
--   `BookProof.SymmetryEntropy.bornCol_eq_zero_iff` (U : Fin n → Fin n → ℂ) (a k : Fin n) : bornCol U a k = 0 ↔ U k a = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSymmetryEntropy`.
--
--   `BookProof.SymmetryEntropy.bornCol_eq_zero_iff` (U : Fin n → Fin n → ℂ) (a k : Fin n) : bornCol U a k = 0 ↔ U k a = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SymmetryEntropy.bornCol_eq_zero_iff`.

-- Generated from ChapterSymmetryEntropy.lean — theorem BookProof.SymmetryEntropy.bornCol_eq_zero_iff
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterReconstruct
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
open BookProof.SymmetryEntropy



open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

theorem BookProof.SymmetryEntropy.bornCol_eq_zero_iff (U : Fin n → Fin n → ℂ) (a k : Fin n) :
    bornCol U a k = 0 ↔ U k a = 0 := by sorry
