-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_add_single_sub_single
-- name    : BookProof.NavierStokesFlow.FockOfFock.add_single_sub_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:11:39.372714+00:00
-- url     : https://prove2.me/theorems/293d2dd5-2dcf-4619-927f-1fa6d7fc5e8d
-- title:
--   (m : M) (n : Conf M) : (n + Finsupp.single m 1 : Conf M) - Finsupp.single m 1 = n
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.add_single_sub_single` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.add_single_sub_single
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.add_single_sub_single (m : M) (n : Conf M) :
    (n + Finsupp.single m 1 : Conf M) - Finsupp.single m 1 = n := by sorry
