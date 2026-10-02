-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_krylov_tower
-- name    : BookProof.ChapterH8.sirk_krylov_tower
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T18:43:12.465976+00:00
-- url     : https://prove2.me/theorems/70dcd19c-e4df-44b6-b7bf-78d89fe7c7df
-- title:
--   The Lean 4 theorem `sirk_krylov_tower` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_krylov_tower` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_krylov_tower
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH5
open BookProof.ChapterH5
open BookProof.ChapterH8

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

theorem BookProof.ChapterH8.sirk_krylov_tower (H : E →ₗ[K] E) (v : E) (n : ℕ) :
    krylovSpan H v n ≤ krylovSpan H v (n + 1) := by sorry
