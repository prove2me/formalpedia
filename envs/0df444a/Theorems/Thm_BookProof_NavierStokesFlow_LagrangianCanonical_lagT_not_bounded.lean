-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_lagT_not_bounded
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.lagT_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:16:23.81669+00:00
-- url     : https://prove2.me/theorems/79a55054-28cc-43e4-baad-09f9d0a9c3c5
-- title:
--   (hnu : 0 < nu) : ¬ ∃ C : ℝ, ∀ v : lpFiniteModes Vel, ‖(lagT nu v : L2I Vel)‖ ≤ C * ‖(v : L2I Vel)‖
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.lagT_not_bounded` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagT_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)

theorem BookProof.NavierStokesFlow.LagrangianCanonical.lagT_not_bounded (hnu : 0 < nu) :
    ¬ ∃ C : ℝ, ∀ v : lpFiniteModes Vel,
      ‖(lagT nu v : L2I Vel)‖ ≤ C * ‖(v : L2I Vel)‖ := by sorry
