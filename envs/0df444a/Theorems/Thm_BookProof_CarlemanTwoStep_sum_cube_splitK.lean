-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_sum_cube_splitK
-- name    : BookProof.CarlemanTwoStep.sum_cube_splitK
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:50:07.573834+00:00
-- url     : https://prove2.me/theorems/df55d7cc-d98d-439f-a759-8c6313875bcf
-- title:
--   `BookProof.CarlemanTwoStep.sum_cube_splitK` (d N : ℕ) (i : Fin d) (k : ℕ) (F : (Fin d →₀ ℕ) → ℂ) : ∑ a ∈ cube d N, F a = ∑ a ∈ innK d N i k, F a + ∑ a ∈ faceK d N i k, F a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.sum_cube_splitK` (d N : ℕ) (i : Fin d) (k : ℕ) (F : (Fin d →₀ ℕ) → ℂ) : ∑ a ∈ cube d N, F a = ∑ a ∈ innK d N i k, F a + ∑ a ∈ faceK d N i k, F a
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.sum_cube_splitK`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.sum_cube_splitK
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep



open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

theorem BookProof.CarlemanTwoStep.sum_cube_splitK (d N : ℕ) (i : Fin d) (k : ℕ) (F : (Fin d →₀ ℕ) → ℂ) :
    ∑ a ∈ cube d N, F a = ∑ a ∈ innK d N i k, F a + ∑ a ∈ faceK d N i k, F a := by sorry
