-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_creat_vacuum
-- name    : BookProof.NavierStokesFlow.FockOfFock.creat_vacuum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:15:52.964486+00:00
-- url     : https://prove2.me/theorems/5594cf4e-2c95-42b9-8039-fe3a8f8e1ba9
-- title:
--   (m : M) : creat m (vacuum : FockDom M) = fockBasis (Finsupp.single m 1)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.creat_vacuum` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.creat_vacuum
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.creat_vacuum (m : M) :
    creat m (vacuum : FockDom M) = fockBasis (Finsupp.single m 1) := by sorry
