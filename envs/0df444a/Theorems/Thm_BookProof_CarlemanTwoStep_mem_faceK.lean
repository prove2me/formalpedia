-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_mem_faceK
-- name    : BookProof.CarlemanTwoStep.mem_faceK
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-10T22:30:00.639006+00:00
-- url     : https://prove2.me/theorems/54e37f6d-7b2e-4967-82be-59dc2b82a50f
-- title:
--   The Lean 4 theorem `mem_faceK` in the `ChapterCarlemanTwoStep` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mem_faceK` in the `ChapterCarlemanTwoStep` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCarlemanTwoStep.lean

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.mem_faceK
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep



open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

theorem BookProof.CarlemanTwoStep.mem_faceK {d N : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} :
    a ∈ faceK d N i k ↔ (∀ j, a j ≤ N) ∧ N < a i + k := by sorry
