-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_ccr_ne
-- name    : BookProof.NavierStokesFlow.FockOfFock.ccr_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:13:14.344346+00:00
-- url     : https://prove2.me/theorems/c63d39a5-11ec-4282-ad54-6bf4a05bc2d7
-- title:
--   {m m' : M} (h : m ≠ m') : (annih m).comp (creat m') - (creat m').comp (annih m) = 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.ccr_ne` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.ccr_ne
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.ccr_ne {m m' : M} (h : m ≠ m') :
    (annih m).comp (creat m') - (creat m').comp (annih m) = 0 := by sorry
