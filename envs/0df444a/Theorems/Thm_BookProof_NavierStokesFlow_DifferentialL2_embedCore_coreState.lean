-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_embedCore_coreState
-- name    : BookProof.NavierStokesFlow.DifferentialL2.embedCore_coreState
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:33:40.703983+00:00
-- url     : https://prove2.me/theorems/30650d80-0b1b-4a1e-a5a9-074990d68f23
-- title:
--   The Lean 4 theorem `embedCore_coreState` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `embedCore_coreState` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.embedCore_coreState
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

theorem BookProof.NavierStokesFlow.DifferentialL2.embedCore_coreState (b : Vel) :
    embedCore (coreState b)
      = coreEquiv (((hermiteMvNorm (velIdx b) : ℝ) : ℂ)⁻¹ • hermiteMv (velIdx b)) := by sorry
