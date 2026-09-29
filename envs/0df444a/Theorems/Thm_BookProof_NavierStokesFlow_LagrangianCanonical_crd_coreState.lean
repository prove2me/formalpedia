-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_crd_coreState
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.crd_coreState
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:43:53.147022+00:00
-- url     : https://prove2.me/theorems/a6836d1e-a09e-4a0d-abf4-455922b9d3f9
-- title:
--   (β γ : Vel) : crd (coreState β) γ = if γ = β then 1 else 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.crd_coreState` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.crd_coreState
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)

theorem BookProof.NavierStokesFlow.LagrangianCanonical.crd_coreState (β γ : Vel) : crd (coreState β) γ = if γ = β then 1 else 0 := by sorry
