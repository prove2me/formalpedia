-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_shiftedK_multiplicity
-- name    : BookProof.CarlemanTwoStep.shiftedK_multiplicity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:52:14.794327+00:00
-- url     : https://prove2.me/theorems/cc3b09e0-4e85-4c51-ad54-377c634c4743
-- title:
--   `BookProof.CarlemanTwoStep.shiftedK_multiplicity` (i : Fin d) (k : ℕ) (b : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => b ∈ (faceK d N i k).image (fun a => a + Finsupp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.shiftedK_multiplicity` (i : Fin d) (k : ℕ) (b : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => b ∈ (faceK d N i k).image (fun a => a + Finsupp.single i k))).card) ≤ k
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.shiftedK_multiplicity`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.shiftedK_multiplicity
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

theorem BookProof.CarlemanTwoStep.shiftedK_multiplicity (i : Fin d) (k : ℕ) (b : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter
      (fun N => b ∈ (faceK d N i k).image (fun a => a + Finsupp.single i k))).card) ≤ k := by sorry
