-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_flipU_mem_maxDom_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.flipU_mem_maxDom_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T09:24:23.88632+00:00
-- url     : https://prove2.me/theorems/58ac6153-4f1a-404b-9d1f-239a3f6415cf
-- title:
--   The Lean 4 theorem `flipU_mem_maxDom` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `flipU_mem_maxDom` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_flipU_mem_maxDom`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.flipU_mem_maxDom_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

theorem BookProof.NavierStokesFlow.SignFlip.flipU_mem_maxDom_inc (p : ι → ℕ) (s : ι → ℝ) {x : L2I ι} (hx : x ∈ maxDom s) :
    flipU p x ∈ maxDom s := by sorry
