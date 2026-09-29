-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.SignedShift.listH_essentiallySelfAdjointOn_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:23:10.349993+00:00
-- url     : https://prove2.me/theorems/19140f83-f775-43fc-be30-27c01023716a
-- title:
--   (L : List (SignedHop ι sym)) (hsym : ∀ β, 1 ≤ sym β) : EssentiallySelfAdjointOn (lpFiniteModes ι) ((listH L).comp (Submodule.inclusion (finiteModes_le_maxDom sym)))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.listH_essentiallySelfAdjointOn_core` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.listH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber
open BookProof.NavierStokesFlow.HermiteFarisLavine









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)


































variable {sym : ι → ℝ}

theorem BookProof.NavierStokesFlow.SignedShift.listH_essentiallySelfAdjointOn_core (L : List (SignedHop ι sym)) (hsym : ∀ β, 1 ≤ sym β) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((listH L).comp (Submodule.inclusion (finiteModes_le_maxDom sym))) := by sorry
