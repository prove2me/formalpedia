-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hopH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_essentiallySelfAdjointOn_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:18:15.659919+00:00
-- url     : https://prove2.me/theorems/aad3c021-4dcb-4b53-beb5-778753db3422
-- title:
--   : EssentiallySelfAdjointOn (lpFiniteModes ι) ((hopH S).comp (Submodule.inclusion (finiteModes_le_maxDom sym)))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_essentiallySelfAdjointOn_core` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((hopH S).comp (Submodule.inclusion (finiteModes_le_maxDom sym))) := by sorry
