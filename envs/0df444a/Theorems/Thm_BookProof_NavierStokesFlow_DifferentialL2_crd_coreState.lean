-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_crd_coreState
-- name    : BookProof.NavierStokesFlow.DifferentialL2.crd_coreState
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:27:17.298987+00:00
-- url     : https://prove2.me/theorems/73815256-8bd9-413c-8025-a4304866ccd7
-- title:
--   The Lean 4 theorem `crd_coreState` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `crd_coreState` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.crd_coreState
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

theorem BookProof.NavierStokesFlow.DifferentialL2.crd_coreState (b g : Vel) : crd (coreState b) g = if g = b then 1 else 0 := by sorry
