-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpFiniteModes_ne_top
-- name    : BookProof.NavierStokesFlow.FockOfFock.lpFiniteModes_ne_top
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:52:49.201649+00:00
-- url     : https://prove2.me/theorems/cbfd114c-3f98-4595-b362-a9f4dbd810cb
-- title:
--   (ι : Type*) [Infinite ι] : lpFiniteModes ι ≠ (⊤ : Submodule ℂ (lp (fun _ : ι => ℂ) 2))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.lpFiniteModes_ne_top` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lpFiniteModes_ne_top
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}

theorem BookProof.NavierStokesFlow.FockOfFock.lpFiniteModes_ne_top (ι : Type*) [Infinite ι] :
    lpFiniteModes ι ≠ (⊤ : Submodule ℂ (lp (fun _ : ι => ℂ) 2)) := by sorry
