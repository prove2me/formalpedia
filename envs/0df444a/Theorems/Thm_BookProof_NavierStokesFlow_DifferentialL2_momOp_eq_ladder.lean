-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_momOp_eq_ladder
-- name    : BookProof.NavierStokesFlow.DifferentialL2.momOp_eq_ladder
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:33:18.867383+00:00
-- url     : https://prove2.me/theorems/ecebe4d1-4e37-4827-9c78-555febbf689c
-- title:
--   The Lean 4 theorem `momOp_eq_ladder` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `momOp_eq_ladder` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.momOp_eq_ladder
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

set_option maxHeartbeats 1000000 in
-- Unfolding the core coordinates through three linear equivalences is elaboration-heavy.

theorem BookProof.NavierStokesFlow.DifferentialL2.momOp_eq_ladder (i : Fin 3) :
    momOp i = (Complex.I / 2) • (creOp i - annOp i) := by sorry
