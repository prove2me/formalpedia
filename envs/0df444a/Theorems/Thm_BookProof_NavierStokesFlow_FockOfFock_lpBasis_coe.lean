-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpBasis_coe
-- name    : BookProof.NavierStokesFlow.FockOfFock.lpBasis_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:50:55.871502+00:00
-- url     : https://prove2.me/theorems/08de4b54-1d35-4e90-bc13-5476533c3e28
-- title:
--   [DecidableEq ι] (i j : ι) : (((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j = if j = i then 1 else 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.lpBasis_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lpBasis_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}

theorem BookProof.NavierStokesFlow.FockOfFock.lpBasis_coe [DecidableEq ι] (i j : ι) :
    (((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j
      = if j = i then 1 else 0 := by sorry
