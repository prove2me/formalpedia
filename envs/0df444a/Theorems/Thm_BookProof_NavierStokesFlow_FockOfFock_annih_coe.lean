-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_annih_coe
-- name    : BookProof.NavierStokesFlow.FockOfFock.annih_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:12:28.370079+00:00
-- url     : https://prove2.me/theorems/676b5d4a-5cf6-4a6d-b124-01f1aaae4a01
-- title:
--   (m : M) (f : FockDom M) (n : Conf M) : (((annih m f : FockDom M) : FockL2 M) : Conf M → ℂ) n = (Real.sqrt (n m + 1) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n + Finsupp.single m 1)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.annih_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.annih_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.annih_coe (m : M) (f : FockDom M) (n : Conf M) :
    (((annih m f : FockDom M) : FockL2 M) : Conf M → ℂ) n
      = (Real.sqrt (n m + 1) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n + Finsupp.single m 1) := by sorry
