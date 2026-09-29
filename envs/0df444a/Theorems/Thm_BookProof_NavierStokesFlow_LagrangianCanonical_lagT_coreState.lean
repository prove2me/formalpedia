-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_lagT_coreState
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.lagT_coreState
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:25:20.338712+00:00
-- url     : https://prove2.me/theorems/605f31cf-2f00-4c5b-afd6-458c7ed26d40
-- title:
--   (β : Vel) : lagT nu (coreState β) = ((lagLam nu β : ℝ) : ℂ) • coreState β
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.lagT_coreState` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagT_coreState
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)

theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagT_coreState (β : Vel) :
    lagT nu (coreState β) = ((lagLam nu β : ℝ) : ℂ) • coreState β := by sorry
