-- Prove2me | Theorems.Thm_BookProof_ChapterH6_generation_single_exponential
-- name    : BookProof.ChapterH6.generation_single_exponential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:05:08.776071+00:00
-- url     : https://prove2.me/theorems/a3e0d6c6-93bc-48c4-a11f-9a107ed97cfd
-- title:
--   The Lean 4 theorem `generation_single_exponential` in the `ChapterH6` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `generation_single_exponential` in the `ChapterH6` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH6.lean

-- Generated from ChapterH6.lean — theorem BookProof.ChapterH6.generation_single_exponential
import Mathlib
import Definitions.Def_ChapterH6
open BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {m : ℕ}


noncomputable section

open Filter Topology

theorem BookProof.ChapterH6.generation_single_exponential (A : Matrix (Fin m) (Fin m) ℂ) (psi0 : Fin m → ℂ) :
    generatedState A 1 psi0 = (NormedSpace.exp ((-Complex.I) • A)).mulVec psi0 := by sorry
