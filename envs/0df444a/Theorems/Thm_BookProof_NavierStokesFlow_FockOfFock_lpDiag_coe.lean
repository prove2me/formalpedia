-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_coe
-- name    : BookProof.NavierStokesFlow.FockOfFock.lpDiag_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:52:22.821987+00:00
-- url     : https://prove2.me/theorems/6e74f9d1-a2e2-4ad9-8ac2-27287a8859a1
-- title:
--   (c : ι → ℝ) (f : lpFiniteModes ι) (i : ι) : (((lpDiag c f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i = (c i : ℂ) * ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.lpDiag_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lpDiag_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}

theorem BookProof.NavierStokesFlow.FockOfFock.lpDiag_coe (c : ι → ℝ) (f : lpFiniteModes ι) (i : ι) :
    (((lpDiag c f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i
      = (c i : ℂ) * ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i := by sorry
