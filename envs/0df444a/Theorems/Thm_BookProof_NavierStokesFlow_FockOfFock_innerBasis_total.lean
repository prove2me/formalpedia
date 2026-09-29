-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_innerBasis_total
-- name    : BookProof.NavierStokesFlow.FockOfFock.innerBasis_total
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:57:21.546741+00:00
-- url     : https://prove2.me/theorems/d76b3e47-24c1-4018-a890-c8ec61c988fe
-- title:
--   (w : FockL2 K) (hw : ∀ c : Conf K, (inner ℂ ((fockBasis c : FockDom K) : FockL2 K) w : ℂ) = 0) : w = 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.innerBasis_total` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.innerBasis_total
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}











variable {M : Type*} [DecidableEq M]

































variable {J K : Type*} [DecidableEq J] [DecidableEq K]

theorem BookProof.NavierStokesFlow.FockOfFock.innerBasis_total (w : FockL2 K)
    (hw : ∀ c : Conf K, (inner ℂ ((fockBasis c : FockDom K) : FockL2 K) w : ℂ) = 0) : w = 0 := by sorry
