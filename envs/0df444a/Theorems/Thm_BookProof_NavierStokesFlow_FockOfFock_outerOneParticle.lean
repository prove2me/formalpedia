-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_outerOneParticle
-- name    : BookProof.NavierStokesFlow.FockOfFock.outerOneParticle
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:16:44.764441+00:00
-- url     : https://prove2.me/theorems/4384c869-2a5c-4b02-bb6b-fad65619b3e2
-- title:
--   (j : J) (c : Conf K) : creat (j, c) (vacuum : FockOfFockDom J K) = fockBasis (Finsupp.single (j, c) 1)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.outerOneParticle` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.outerOneParticle
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

































variable {J K : Type*} [DecidableEq J] [DecidableEq K]

theorem BookProof.NavierStokesFlow.FockOfFock.outerOneParticle (j : J) (c : Conf K) :
    creat (j, c) (vacuum : FockOfFockDom J K) = fockBasis (Finsupp.single (j, c) 1) := by sorry
