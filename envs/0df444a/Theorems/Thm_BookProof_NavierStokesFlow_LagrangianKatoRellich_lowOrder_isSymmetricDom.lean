-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_lowOrder_isSymmetricDom
-- name    : BookProof.NavierStokesFlow.LagrangianKatoRellich.lowOrder_isSymmetricDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:54:32.383915+00:00
-- url     : https://prove2.me/theorems/79df0e70-3892-43d0-a4f9-f1a841823225
-- title:
--   The Lean 4 theorem `lowOrder_isSymmetricDom` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `lowOrder_isSymmetricDom` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianKatoRellich.lean

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.lowOrder_isSymmetricDom
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

theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.lowOrder_isSymmetricDom : IsSymmetricDom (lowOrder L) := by sorry
