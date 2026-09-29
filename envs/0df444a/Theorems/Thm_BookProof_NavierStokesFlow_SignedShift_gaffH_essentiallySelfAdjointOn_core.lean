-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_gaffH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.SignedShift.gaffH_essentiallySelfAdjointOn_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:24:27.154728+00:00
-- url     : https://prove2.me/theorems/c9a27133-d420-4638-a0bb-af5314734500
-- title:
--   : EssentiallySelfAdjointOn (lpFiniteModes ℕ) ((gaffH kap cst).comp (Submodule.inclusion (finiteModes_le_maxDom (gsym kap cst))))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.gaffH_essentiallySelfAdjointOn_core` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.gaffH_essentiallySelfAdjointOn_core
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















variable (kap cst : ℝ)

theorem BookProof.NavierStokesFlow.SignedShift.gaffH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((gaffH kap cst).comp (Submodule.inclusion (finiteModes_le_maxDom (gsym kap cst)))) := by sorry
