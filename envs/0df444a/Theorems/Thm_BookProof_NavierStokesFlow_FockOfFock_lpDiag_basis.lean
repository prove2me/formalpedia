-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_basis
-- name    : BookProof.NavierStokesFlow.FockOfFock.lpDiag_basis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:57:02.069384+00:00
-- url     : https://prove2.me/theorems/d2e46ebc-e6b4-4f49-acd8-49d533a92176
-- title:
--   [DecidableEq ι] (c : ι → ℝ) (i : ι) : lpDiag c (lpBasis i) = ((c i : ℝ) : ℂ) • lpBasis i
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.lpDiag_basis` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lpDiag_basis
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}

theorem BookProof.NavierStokesFlow.FockOfFock.lpDiag_basis [DecidableEq ι] (c : ι → ℝ) (i : ι) :
    lpDiag c (lpBasis i) = ((c i : ℝ) : ℂ) • lpBasis i := by sorry
