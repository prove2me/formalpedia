-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_fockBasis_coe
-- name    : BookProof.NavierStokesFlow.FockOfFock.fockBasis_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:56:54.153579+00:00
-- url     : https://prove2.me/theorems/e5595905-3e57-4217-b8b2-e590a55e5ad5
-- title:
--   (n k : Conf M) : (((fockBasis n : FockDom M) : FockL2 M) : Conf M → ℂ) k = if k = n then 1 else 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.fockBasis_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.fockBasis_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.fockBasis_coe (n k : Conf M) :
    (((fockBasis n : FockDom M) : FockL2 M) : Conf M → ℂ) k = if k = n then 1 else 0 := by sorry
