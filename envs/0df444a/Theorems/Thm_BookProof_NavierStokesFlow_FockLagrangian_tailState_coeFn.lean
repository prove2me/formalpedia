-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_tailState_coeFn
-- name    : BookProof.NavierStokesFlow.FockLagrangian.tailState_coeFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:49:56.168976+00:00
-- url     : https://prove2.me/theorems/c23a404c-4b57-4714-ac8b-147d8eee6ec4
-- title:
--   `BookProof.NavierStokesFlow.FockLagrangian.tailState_coeFn` : ((tailState : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ) =ᵐ[fockR] tailFockSet.indicator (fun _ => (1 : ℂ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockParcels`.
--
--   `BookProof.NavierStokesFlow.FockLagrangian.tailState_coeFn` : ((tailState : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ) =ᵐ[fockR] tailFockSet.indicator (fun _ => (1 : ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockLagrangian.tailState_coeFn`.

-- Generated from ChapterNavierStokesFockParcels.lean — theorem BookProof.NavierStokesFlow.FockLagrangian.tailState_coeFn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian


open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.NavierStokesFlow.FockLagrangian.tailState_coeFn :
    ((tailState : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ)
      =ᵐ[fockR] tailFockSet.indicator (fun _ => (1 : ℂ)) := by sorry
