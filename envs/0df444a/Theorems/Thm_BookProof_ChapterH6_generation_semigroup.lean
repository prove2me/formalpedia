-- Prove2me | Theorems.Thm_BookProof_ChapterH6_generation_semigroup
-- name    : BookProof.ChapterH6.generation_semigroup
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:05:02.894781+00:00
-- url     : https://prove2.me/theorems/1936b24f-e4ba-466d-ad48-568676c37c51
-- title:
--   The Lean 4 theorem `generation_semigroup` in the `ChapterH6` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `generation_semigroup` in the `ChapterH6` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH6.lean

-- Generated from ChapterH6.lean — theorem BookProof.ChapterH6.generation_semigroup
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

theorem BookProof.ChapterH6.generation_semigroup (A : Matrix (Fin m) (Fin m) ℂ) (s t : ℂ)
    (psi0 : Fin m → ℂ) :
    generatedState A (s + t) psi0 = generatedState A s (generatedState A t psi0) := by sorry
