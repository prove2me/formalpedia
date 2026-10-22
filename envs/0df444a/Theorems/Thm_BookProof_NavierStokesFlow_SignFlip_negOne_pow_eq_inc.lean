-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_negOne_pow_eq_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.negOne_pow_eq_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T09:24:35.732819+00:00
-- url     : https://prove2.me/theorems/a32030eb-e0b0-424a-996c-70ec5105d2dd
-- title:
--   The Lean 4 theorem `negOne_pow_eq` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `negOne_pow_eq` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_negOne_pow_eq`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.negOne_pow_eq_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

theorem BookProof.NavierStokesFlow.SignFlip.negOne_pow_eq_inc (k : ℕ) : (-1 : ℂ) ^ k = 1 ∨ (-1 : ℂ) ^ k = -1 := by sorry
