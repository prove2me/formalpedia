-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_norm_lpBasis
-- name    : BookProof.NavierStokesFlow.FockOfFock.norm_lpBasis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:52:50.557564+00:00
-- url     : https://prove2.me/theorems/3aeb43a3-5f0f-4df9-b41d-b3b90a06332c
-- title:
--   [DecidableEq ι] (i : ι) : ‖lpBasis (ι
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.norm_lpBasis` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.norm_lpBasis
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}

theorem BookProof.NavierStokesFlow.FockOfFock.norm_lpBasis [DecidableEq ι] (i : ι) : ‖lpBasis (ι := ι) i‖ = 1 := by sorry
