-- Prove2me | Theorems.Thm_BookProof_SymmetryEntropy_bornCol_nonneg
-- name    : BookProof.SymmetryEntropy.bornCol_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:02:34.124244+00:00
-- url     : https://prove2.me/theorems/53e217b5-6974-4d1d-a63d-d913234391a7
-- title:
--   `BookProof.SymmetryEntropy.bornCol_nonneg` (U : Fin n → Fin n → ℂ) (a : Fin n) (k : Fin n) : 0 ≤ bornCol U a k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSymmetryEntropy`.
--
--   `BookProof.SymmetryEntropy.bornCol_nonneg` (U : Fin n → Fin n → ℂ) (a : Fin n) (k : Fin n) : 0 ≤ bornCol U a k
--
--   Formalization note: Lean 4 identifier `BookProof.SymmetryEntropy.bornCol_nonneg`.

-- Generated from ChapterSymmetryEntropy.lean — theorem BookProof.SymmetryEntropy.bornCol_nonneg
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterReconstruct
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
open BookProof.SymmetryEntropy



open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

theorem BookProof.SymmetryEntropy.bornCol_nonneg (U : Fin n → Fin n → ℂ) (a : Fin n) (k : Fin n) :
    0 ≤ bornCol U a k := by sorry
