-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_mem_innK
-- name    : BookProof.CarlemanTwoStep.mem_innK
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T22:31:40.662202+00:00
-- url     : https://prove2.me/theorems/6b8f11fe-878c-467b-b98f-ef6969306f92
-- title:
--   The Lean 4 theorem `mem_innK` in the `ChapterCarlemanTwoStep` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mem_innK` in the `ChapterCarlemanTwoStep` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCarlemanTwoStep.lean

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.mem_innK
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep



open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

theorem BookProof.CarlemanTwoStep.mem_innK {d N : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} :
    a ∈ innK d N i k ↔ (∀ j, a j ≤ N) ∧ a i + k ≤ N := by sorry
