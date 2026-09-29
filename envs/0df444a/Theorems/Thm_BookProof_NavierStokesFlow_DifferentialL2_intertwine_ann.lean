-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwine_ann
-- name    : BookProof.NavierStokesFlow.DifferentialL2.intertwine_ann
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:30:36.658806+00:00
-- url     : https://prove2.me/theorems/27db0d1e-9ea8-4838-a4fb-0407de0bde3d
-- title:
--   The Lean 4 theorem `intertwine_ann` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `intertwine_ann` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.intertwine_ann
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

theorem BookProof.NavierStokesFlow.DifferentialL2.intertwine_ann (i : Fin 3) : (annOp i).comp embedCore = embedCore.comp (ann i) := by sorry
