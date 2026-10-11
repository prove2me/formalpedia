-- Prove2me | Theorems.Thm_BookProof_SymmetryEntropy_bornCol_le_one
-- name    : BookProof.SymmetryEntropy.bornCol_le_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:05:05.031026+00:00
-- url     : https://prove2.me/theorems/2382d916-38e9-43b6-aa34-88b740e89bca
-- title:
--   `BookProof.SymmetryEntropy.bornCol_le_one` {U : Fin n → Fin n → ℂ} {a : Fin n} (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (k : Fin n) : bornCol U a k ≤ 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSymmetryEntropy`.
--
--   `BookProof.SymmetryEntropy.bornCol_le_one` {U : Fin n → Fin n → ℂ} {a : Fin n} (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (k : Fin n) : bornCol U a k ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.SymmetryEntropy.bornCol_le_one`.

-- Generated from ChapterSymmetryEntropy.lean — theorem BookProof.SymmetryEntropy.bornCol_le_one
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterReconstruct
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
open BookProof.SymmetryEntropy



open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

theorem BookProof.SymmetryEntropy.bornCol_le_one {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (k : Fin n) : bornCol U a k ≤ 1 := by sorry
