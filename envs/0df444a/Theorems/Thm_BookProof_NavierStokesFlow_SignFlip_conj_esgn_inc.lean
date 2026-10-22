-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_conj_esgn_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.conj_esgn_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T09:23:03.120971+00:00
-- url     : https://prove2.me/theorems/ad07a6b3-08cd-412c-ab0c-a6d6a75c7c67
-- title:
--   The Lean 4 theorem `conj_esgn` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `conj_esgn` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_conj_esgn`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.conj_esgn_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

theorem BookProof.NavierStokesFlow.SignFlip.conj_esgn_inc (c : ℝ) : (starRingEnd ℂ) (esgn c) = esgn c := by sorry
