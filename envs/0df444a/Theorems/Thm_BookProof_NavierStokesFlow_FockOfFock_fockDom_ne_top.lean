-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_fockDom_ne_top
-- name    : BookProof.NavierStokesFlow.FockOfFock.fockDom_ne_top
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:57:28.456295+00:00
-- url     : https://prove2.me/theorems/608581f3-0d6e-4a7d-8fbb-b7952f364547
-- title:
--   [Nonempty M] : (FockDom M : Submodule ℂ (FockL2 M)) ≠ ⊤
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.fockDom_ne_top` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.fockDom_ne_top
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.fockDom_ne_top [Nonempty M] :
    (FockDom M : Submodule ℂ (FockL2 M)) ≠ ⊤ := by sorry
