-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_creat_basis
-- name    : BookProof.NavierStokesFlow.FockOfFock.creat_basis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:13.790267+00:00
-- url     : https://prove2.me/theorems/126d7d97-5be2-402e-ae09-ee358d65c6b7
-- title:
--   (m : M) (n : Conf M) : creat m (fockBasis n) = ((Real.sqrt (n m + 1) : ℝ) : ℂ) • fockBasis (n + Finsupp.single m 1)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.creat_basis` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.creat_basis
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.creat_basis (m : M) (n : Conf M) :
    creat m (fockBasis n)
      = ((Real.sqrt (n m + 1) : ℝ) : ℂ) • fockBasis (n + Finsupp.single m 1) := by sorry
