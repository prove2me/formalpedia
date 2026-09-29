-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_coeffOp_coe
-- name    : BookProof.NavierStokesFlow.FockOfFock.coeffOp_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:50:28.359159+00:00
-- url     : https://prove2.me/theorems/f58ede53-7e9a-478f-a8c5-7a506c903ee6
-- title:
--   (T : (ι → ℂ) → ι → ℂ) (hsupp) (hadd) (hsmul) (f : lpFiniteModes ι) : (((coeffOp T hsupp hadd hsmul f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) = T ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.coeffOp_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.coeffOp_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}

theorem BookProof.NavierStokesFlow.FockOfFock.coeffOp_coe (T : (ι → ℂ) → ι → ℂ) (hsupp) (hadd) (hsmul) (f : lpFiniteModes ι) :
    (((coeffOp T hsupp hadd hsmul f : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ)
      = T ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) := by sorry
