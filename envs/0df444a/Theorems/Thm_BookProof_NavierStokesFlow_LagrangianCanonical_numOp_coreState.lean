-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_numOp_coreState
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.numOp_coreState
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:36:05.093575+00:00
-- url     : https://prove2.me/theorems/ee7e39d5-6cd4-45c2-bbd5-6f02324e9cba
-- title:
--   (i : Fin 3) (β : Vel) : numOp i (coreState β) = ((β i : ℝ) : ℂ) • coreState β
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.numOp_coreState` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.numOp_coreState
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)

theorem BookProof.NavierStokesFlow.LagrangianCanonical.numOp_coreState (i : Fin 3) (β : Vel) :
    numOp i (coreState β) = ((β i : ℝ) : ℂ) • coreState β := by sorry
