-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_faceK_multiplicity
-- name    : BookProof.CarlemanTwoStep.faceK_multiplicity
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:52:44.665593+00:00
-- url     : https://prove2.me/theorems/5242a0d5-8732-4a80-af92-a9aadda59f97
-- title:
--   `BookProof.CarlemanTwoStep.faceK_multiplicity` (i : Fin d) (k : ℕ) (a : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => a ∈ faceK d N i k)).card) ≤ k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.faceK_multiplicity` (i : Fin d) (k : ℕ) (a : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => a ∈ faceK d N i k)).card) ≤ k
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.faceK_multiplicity`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.faceK_multiplicity
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanTwoStep



open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}

theorem BookProof.CarlemanTwoStep.faceK_multiplicity (i : Fin d) (k : ℕ) (a : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter (fun N => a ∈ faceK d N i k)).card) ≤ k := by sorry
