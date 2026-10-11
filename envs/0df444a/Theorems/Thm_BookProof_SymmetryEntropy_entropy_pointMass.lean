-- Prove2me | Theorems.Thm_BookProof_SymmetryEntropy_entropy_pointMass
-- name    : BookProof.SymmetryEntropy.entropy_pointMass
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:03:15.772983+00:00
-- url     : https://prove2.me/theorems/5171b1d8-5c82-4122-a675-fc462b8ed81e
-- title:
--   `BookProof.SymmetryEntropy.entropy_pointMass` (a : Fin n) : entropy (fun k => if k = a then (1 : ℝ) else 0) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSymmetryEntropy`.
--
--   `BookProof.SymmetryEntropy.entropy_pointMass` (a : Fin n) : entropy (fun k => if k = a then (1 : ℝ) else 0) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SymmetryEntropy.entropy_pointMass`.

-- Generated from ChapterSymmetryEntropy.lean — theorem BookProof.SymmetryEntropy.entropy_pointMass
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

theorem BookProof.SymmetryEntropy.entropy_pointMass (a : Fin n) :
    entropy (fun k => if k = a then (1 : ℝ) else 0) = 0 := by sorry
