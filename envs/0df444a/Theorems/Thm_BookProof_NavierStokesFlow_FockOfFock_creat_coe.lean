-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_creat_coe
-- name    : BookProof.NavierStokesFlow.FockOfFock.creat_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:50:31.195994+00:00
-- url     : https://prove2.me/theorems/94e8c742-ba97-48ba-b91e-4032f7a54813
-- title:
--   (m : M) (f : FockDom M) (n : Conf M) : (((creat m f : FockDom M) : FockL2 M) : Conf M → ℂ) n = (Real.sqrt (n m) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n - Finsupp.single m 1)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.creat_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.creat_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.creat_coe (m : M) (f : FockDom M) (n : Conf M) :
    (((creat m f : FockDom M) : FockL2 M) : Conf M → ℂ) n
      = (Real.sqrt (n m) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n - Finsupp.single m 1) := by sorry
