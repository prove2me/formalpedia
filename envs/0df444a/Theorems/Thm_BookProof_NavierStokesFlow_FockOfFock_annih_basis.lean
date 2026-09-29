-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_annih_basis
-- name    : BookProof.NavierStokesFlow.FockOfFock.annih_basis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:12:50.374414+00:00
-- url     : https://prove2.me/theorems/eac99685-0b88-4937-927d-29f85d9b1feb
-- title:
--   (m : M) (n : Conf M) : annih m (fockBasis n) = ((Real.sqrt (n m) : ℝ) : ℂ) • fockBasis (n - Finsupp.single m 1)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.annih_basis` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.annih_basis
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.annih_basis (m : M) (n : Conf M) :
    annih m (fockBasis n) = ((Real.sqrt (n m) : ℝ) : ℂ) • fockBasis (n - Finsupp.single m 1) := by sorry
