-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FockOfFock.lpDiag_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:03:02.825536+00:00
-- url     : https://prove2.me/theorems/90deeece-a52e-4f61-bd1b-34659749f6a6
-- title:
--   (c : ι → ℝ) : HasZeroDeficiencyOn (lpFiniteModes ι) (lpDiag c)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.lpDiag_hasZeroDeficiencyOn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lpDiag_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}

theorem BookProof.NavierStokesFlow.FockOfFock.lpDiag_hasZeroDeficiencyOn (c : ι → ℝ) :
    HasZeroDeficiencyOn (lpFiniteModes ι) (lpDiag c) := by sorry
