-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwined_pos
-- name    : BookProof.NavierStokesFlow.DifferentialL2.intertwined_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:32:57.844155+00:00
-- url     : https://prove2.me/theorems/3ac5291b-1c84-40e4-be7d-9c3ebb2001d1
-- title:
--   The Lean 4 theorem `intertwined_pos` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `intertwined_pos` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.intertwined_pos
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

set_option maxHeartbeats 4000000 in
-- The transport arguments unfold operators on a submodule of `L²(ℝ³)` through several
-- linear equivalences, so the default heartbeat budget is not enough.

theorem BookProof.NavierStokesFlow.DifferentialL2.intertwined_pos (i : Fin 3) :
    Intertwined (pos i) (((1 / Real.sqrt 2 : ℝ) : ℂ) • posOp i) := by sorry
