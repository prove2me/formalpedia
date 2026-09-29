-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwine_cre
-- name    : BookProof.NavierStokesFlow.DifferentialL2.intertwine_cre
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:31:22.189395+00:00
-- url     : https://prove2.me/theorems/c3941a40-840b-4c96-9749-3b5f592b4a4b
-- title:
--   The Lean 4 theorem `intertwine_cre` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `intertwine_cre` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.intertwine_cre
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

theorem BookProof.NavierStokesFlow.DifferentialL2.intertwine_cre (i : Fin 3) : (creOp i).comp embedCore = embedCore.comp (cre i) := by sorry
