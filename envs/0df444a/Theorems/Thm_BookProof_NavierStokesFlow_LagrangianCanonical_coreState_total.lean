-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_coreState_total
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.coreState_total
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:43:11.38679+00:00
-- url     : https://prove2.me/theorems/8a32d24d-d3a7-41fc-8ca0-5b7c8cd590c6
-- title:
--   (w : L2I Vel) (hw : ∀ β : Vel, (inner ℂ ((coreState β : lpFiniteModes Vel) : L2I Vel) w : ℂ) = 0) : w = 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.coreState_total` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.coreState_total
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)

theorem BookProof.NavierStokesFlow.LagrangianCanonical.coreState_total (w : L2I Vel)
    (hw : ∀ β : Vel, (inner ℂ ((coreState β : lpFiniteModes Vel) : L2I Vel) w : ℂ) = 0) :
    w = 0 := by sorry
