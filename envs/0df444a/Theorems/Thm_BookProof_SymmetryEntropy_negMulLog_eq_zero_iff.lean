-- Prove2me | Theorems.Thm_BookProof_SymmetryEntropy_negMulLog_eq_zero_iff
-- name    : BookProof.SymmetryEntropy.negMulLog_eq_zero_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:02:01.352463+00:00
-- url     : https://prove2.me/theorems/96a4ae90-1d12-4ab4-b6ea-bf7422b3772a
-- title:
--   `BookProof.SymmetryEntropy.negMulLog_eq_zero_iff` {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.negMulLog x = 0 ↔ x = 0 ∨ x = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSymmetryEntropy`.
--
--   `BookProof.SymmetryEntropy.negMulLog_eq_zero_iff` {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.negMulLog x = 0 ↔ x = 0 ∨ x = 1
--
--   Formalization note: Lean 4 identifier `BookProof.SymmetryEntropy.negMulLog_eq_zero_iff`.

-- Generated from ChapterSymmetryEntropy.lean — theorem BookProof.SymmetryEntropy.negMulLog_eq_zero_iff
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterReconstruct
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
open BookProof.SymmetryEntropy



open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

theorem BookProof.SymmetryEntropy.negMulLog_eq_zero_iff {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.negMulLog x = 0 ↔ x = 0 ∨ x = 1 := by sorry
