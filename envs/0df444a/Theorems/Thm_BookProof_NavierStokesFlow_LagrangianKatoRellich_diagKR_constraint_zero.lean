-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_diagKR_constraint_zero
-- name    : BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_constraint_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:10:59.506136+00:00
-- url     : https://prove2.me/theorems/d69df243-e6e1-4d3e-a90f-5d5e329524ae
-- title:
--   The Lean 4 theorem `diagKR_constraint_zero` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagKR_constraint_zero` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianKatoRellich.lean

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_constraint_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterSirkBandLedger
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich
open Filter Topology
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)


























variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (L : LagrangianFullData F)








open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.DiagonalEsa

theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_constraint_zero : diagKR.constraintOp = 0 := by sorry
