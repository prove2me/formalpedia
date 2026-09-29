-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpBasis_total
-- name    : BookProof.NavierStokesFlow.FockOfFock.lpBasis_total
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:52:18.519378+00:00
-- url     : https://prove2.me/theorems/6cc7392a-037a-42d9-aee5-4ab1bb9d44f2
-- title:
--   [DecidableEq ι] (w : lp (fun _ : ι => ℂ) 2) (hw : ∀ i, (inner ℂ ((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) w : ℂ) = 0) : w = 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.lpBasis_total` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lpBasis_total
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}

theorem BookProof.NavierStokesFlow.FockOfFock.lpBasis_total [DecidableEq ι] (w : lp (fun _ : ι => ℂ) 2)
    (hw : ∀ i, (inner ℂ ((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) w : ℂ) = 0) :
    w = 0 := by sorry
