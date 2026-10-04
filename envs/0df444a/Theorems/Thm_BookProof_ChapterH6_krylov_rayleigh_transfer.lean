-- Prove2me | Theorems.Thm_BookProof_ChapterH6_krylov_rayleigh_transfer
-- name    : BookProof.ChapterH6.krylov_rayleigh_transfer
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T10:14:34.65144+00:00
-- url     : https://prove2.me/theorems/052b4c1a-cdbf-49b8-b772-5995077d8ab6
-- title:
--   The Lean 4 theorem `krylov_rayleigh_transfer` in the `ChapterH6` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `krylov_rayleigh_transfer` in the `ChapterH6` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH6.lean

-- Generated from ChapterH6.lean — theorem BookProof.ChapterH6.krylov_rayleigh_transfer
import Mathlib
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4
open BookProof.ChapterH4
open BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]


noncomputable section

open Filter Topology

theorem BookProof.ChapterH6.krylov_rayleigh_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E) (y : F) :
    inner ℂ y (compress V X y) = inner ℂ (V y) (X (V y)) := by sorry
