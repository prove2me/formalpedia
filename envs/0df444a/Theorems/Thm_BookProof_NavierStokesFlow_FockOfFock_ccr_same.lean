-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_ccr_same
-- name    : BookProof.NavierStokesFlow.FockOfFock.ccr_same
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:56:26.52583+00:00
-- url     : https://prove2.me/theorems/244678a2-3bf1-493d-aa4f-314b2ab07c1a
-- title:
--   (m : M) : (annih m).comp (creat m) - (creat m).comp (annih m) = LinearMap.id (R
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.ccr_same` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.ccr_same
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.ccr_same (m : M) :
    (annih m).comp (creat m) - (creat m).comp (annih m)
      = LinearMap.id (R := ℂ) (M := FockDom M) := by sorry
