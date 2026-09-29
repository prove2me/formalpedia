-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_annih_vacuum
-- name    : BookProof.NavierStokesFlow.FockOfFock.annih_vacuum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:16:02.186388+00:00
-- url     : https://prove2.me/theorems/2009dd59-cb31-4a8c-bc16-87a70723d53d
-- title:
--   (m : M) : annih m (vacuum : FockDom M) = 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.annih_vacuum` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.annih_vacuum
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.annih_vacuum (m : M) : annih m (vacuum : FockDom M) = 0 := by sorry
