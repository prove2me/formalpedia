-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velH_coe_single
-- name    : BookProof.NavierStokesFlow.ThreeComponent.velH_coe_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:11:52.295063+00:00
-- url     : https://prove2.me/theorems/92aed139-3c3d-45fe-b52e-a03ec88affa4
-- title:
--   The Lean 4 theorem `velH_coe_single` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velH_coe_single` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.velH_coe_single
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.velH_coe_single (β γ : Vel) :
    ((velH A c (velState A c β) : L2I Vel) : Vel → ℂ) γ
      = ((hopList A c).map (fun S => Complex.I *
          ((if γ = S.shift β then (S.amp β : ℂ) else 0)
            - (if S.shift γ = β then (S.amp γ : ℂ) else 0)))).sum := by sorry
