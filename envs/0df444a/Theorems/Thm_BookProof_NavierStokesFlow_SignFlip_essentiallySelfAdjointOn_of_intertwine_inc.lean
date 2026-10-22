-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_essentiallySelfAdjointOn_of_intertwine_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.essentiallySelfAdjointOn_of_intertwine_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T09:23:51.226034+00:00
-- url     : https://prove2.me/theorems/3a7b397a-a82d-4093-ab56-54d5b78cf607
-- title:
--   The Lean 4 theorem `essentiallySelfAdjointOn_of_intertwine` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `essentiallySelfAdjointOn_of_intertwine` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_essentiallySelfAdjointOn_of_intertwine`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.essentiallySelfAdjointOn_of_intertwine_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.NavierStokesFlow.SignFlip.essentiallySelfAdjointOn_of_intertwine_inc (U : F ≃ₗᵢ[ℂ] F) (T T' : D →ₗ[ℂ] F)
    (hU : ∀ v : D, U (v : F) ∈ D)
    (hcomm : ∀ v : D, U (T v) = T' ⟨U (v : F), hU v⟩)
    (hT : EssentiallySelfAdjointOn D T) : EssentiallySelfAdjointOn D T' := by sorry
