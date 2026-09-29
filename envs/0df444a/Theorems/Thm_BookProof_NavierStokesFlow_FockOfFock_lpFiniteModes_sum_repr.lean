-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpFiniteModes_sum_repr
-- name    : BookProof.NavierStokesFlow.FockOfFock.lpFiniteModes_sum_repr
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:57:13.503103+00:00
-- url     : https://prove2.me/theorems/d6263b86-96e1-4499-82cc-d7ce568d9a53
-- title:
--   {ι : Type*} [DecidableEq ι] (f : lpFiniteModes ι) : f = ∑ i ∈ f.2.toFinset, (((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i) • lpBasis i
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.lpFiniteModes_sum_repr` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lpFiniteModes_sum_repr
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.lpFiniteModes_sum_repr {ι : Type*} [DecidableEq ι] (f : lpFiniteModes ι) :
    f = ∑ i ∈ f.2.toFinset, (((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i) • lpBasis i := by sorry
