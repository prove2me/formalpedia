-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_coe
-- name    : BookProof.NavierStokesFlow.SignedShift.listH_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:49:16.57051+00:00
-- url     : https://prove2.me/theorems/fa275501-e9d2-4a60-95eb-52688b7b1ca0
-- title:
--   {sym : ι → ℝ} (L : List (SignedHop ι sym)) (x : maxDom sym) (γ : ι) : ((listH L x : L2I ι) : ι → ℂ) γ = (L.map (fun S => S.hFun ((x : L2I ι) : ι → ℂ) γ)).sum
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.listH_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.listH_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber
open BookProof.NavierStokesFlow.HermiteFarisLavine









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)


































variable {sym : ι → ℝ}

theorem BookProof.NavierStokesFlow.SignedShift.listH_coe {sym : ι → ℝ} (L : List (SignedHop ι sym)) (x : maxDom sym) (γ : ι) :
    ((listH L x : L2I ι) : ι → ℂ) γ
      = (L.map (fun S => S.hFun ((x : L2I ι) : ι → ℂ) γ)).sum := by sorry
