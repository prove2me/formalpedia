-- Prove2me | Theorems.Thm_BookProof_SymmetryEntropy_entropy_bornCol_pos_iff_not_isDeterministicCol
-- name    : BookProof.SymmetryEntropy.entropy_bornCol_pos_iff_not_isDeterministicCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:03:16.843975+00:00
-- url     : https://prove2.me/theorems/457c9186-7fa5-4259-99d3-05ad38914523
-- title:
--   `BookProof.SymmetryEntropy.entropy_bornCol_pos_iff_not_isDeterministicCol` {U : Fin n → Fin n → ℂ} {a : Fin n} (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) : 0 < entropy (bornCol U a) ↔ ¬ IsDeter
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSymmetryEntropy`.
--
--   `BookProof.SymmetryEntropy.entropy_bornCol_pos_iff_not_isDeterministicCol` {U : Fin n → Fin n → ℂ} {a : Fin n} (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) : 0 < entropy (bornCol U a) ↔ ¬ IsDeterministicCol U a
--
--   Formalization note: Lean 4 identifier `BookProof.SymmetryEntropy.entropy_bornCol_pos_iff_not_isDeterministicCol`.

-- Generated from ChapterSymmetryEntropy.lean — theorem BookProof.SymmetryEntropy.entropy_bornCol_pos_iff_not_isDeterministicCol
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

theorem BookProof.SymmetryEntropy.entropy_bornCol_pos_iff_not_isDeterministicCol {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) :
    0 < entropy (bornCol U a) ↔ ¬ IsDeterministicCol U a := by sorry
