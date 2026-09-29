-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_creat_adjoint
-- name    : BookProof.NavierStokesFlow.FockOfFock.creat_adjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:56:31.085819+00:00
-- url     : https://prove2.me/theorems/64b9a667-61ca-4223-a82a-128a17b7d34f
-- title:
--   (m : M) (v w : FockDom M) : (inner ℂ ((creat m v : FockDom M) : FockL2 M) ((w : FockDom M) : FockL2 M) : ℂ) = inner ℂ ((v : FockDom M) : FockL2 M) ((annih m w : FockDom M) : FockL2 M)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.creat_adjoint` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.creat_adjoint
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.creat_adjoint (m : M) (v w : FockDom M) :
    (inner ℂ ((creat m v : FockDom M) : FockL2 M) ((w : FockDom M) : FockL2 M) : ℂ)
      = inner ℂ ((v : FockDom M) : FockL2 M) ((annih m w : FockDom M) : FockL2 M) := by sorry
