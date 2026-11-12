-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_sum_shiftK
-- name    : BookProof.CarlemanTwoStep.sum_shiftK
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T22:33:17.849678+00:00
-- url     : https://prove2.me/theorems/2c1bb4c7-a6bc-4799-bdb7-cf7060f5ff25
-- title:
--   The Lean 4 theorem `sum_shiftK` in the `ChapterCarlemanTwoStep` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sum_shiftK` in the `ChapterCarlemanTwoStep` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCarlemanTwoStep.lean

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.sum_shiftK
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep



open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

theorem BookProof.CarlemanTwoStep.sum_shiftK (d N : ℕ) (i : Fin d) (k : ℕ) (F : (Fin d →₀ ℕ) → ℂ)
    (hF : ∀ a : Fin d →₀ ℕ, a i < k → F a = 0) :
    ∑ a ∈ cube d N, F a = ∑ b ∈ innK d N i k, F (b + Finsupp.single i k) := by sorry
