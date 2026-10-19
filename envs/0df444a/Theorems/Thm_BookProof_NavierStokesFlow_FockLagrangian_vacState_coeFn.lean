-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_vacState_coeFn
-- name    : BookProof.NavierStokesFlow.FockLagrangian.vacState_coeFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:51:49.687468+00:00
-- url     : https://prove2.me/theorems/8587850a-6bd1-4164-b2fd-7f7667b0fdf9
-- title:
--   `BookProof.NavierStokesFlow.FockLagrangian.vacState_coeFn` : ((vacState : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ) =ᵐ[fockR] vacSet.indicator (fun _ => (1 : ℂ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockParcels`.
--
--   `BookProof.NavierStokesFlow.FockLagrangian.vacState_coeFn` : ((vacState : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ) =ᵐ[fockR] vacSet.indicator (fun _ => (1 : ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockLagrangian.vacState_coeFn`.

-- Generated from ChapterNavierStokesFockParcels.lean — theorem BookProof.NavierStokesFlow.FockLagrangian.vacState_coeFn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian


open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.NavierStokesFlow.FockLagrangian.vacState_coeFn :
    ((vacState : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ)
      =ᵐ[fockR] vacSet.indicator (fun _ => (1 : ℂ)) := by sorry
