-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_ofCoeff_coe
-- name    : BookProof.NavierStokesFlow.FockOfFock.ofCoeff_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:53:00.126752+00:00
-- url     : https://prove2.me/theorems/99e566c3-06e7-4fd5-a03b-bf3c46ddca85
-- title:
--   (φ : ι → ℂ) (h : (Function.support φ).Finite) : (((ofCoeff φ h : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) = φ
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.ofCoeff_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.ofCoeff_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}

theorem BookProof.NavierStokesFlow.FockOfFock.ofCoeff_coe (φ : ι → ℂ) (h : (Function.support φ).Finite) :
    (((ofCoeff φ h : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) = φ := by sorry
