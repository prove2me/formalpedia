-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_diagKR_secondOrder
-- name    : BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_secondOrder
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:55:35.053233+00:00
-- url     : https://prove2.me/theorems/0aec7fe8-0798-4a78-8ef1-ea7d08d3024b
-- title:
--   The Lean 4 theorem `diagKR_secondOrder` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagKR_secondOrder` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianKatoRellich.lean

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_secondOrder
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterSirkBandLedger
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich
















open Filter Topology



open FullEsa LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)


























variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (L : LagrangianFullData F)








open LpNat DiagonalEsa

theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_secondOrder :
    secondOrder diagKR = diagOp (fun n => (3 / 2 : ℝ) * (n : ℝ) ^ 2) := by sorry
