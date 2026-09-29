-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_lagrangianCore_symmetricOn
-- name    : BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangianCore_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:54:23.450049+00:00
-- url     : https://prove2.me/theorems/a0e5a318-33ff-4804-8ebd-23fc139147d1
-- title:
--   The Lean 4 theorem `lagrangianCore_symmetricOn` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `lagrangianCore_symmetricOn` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianKatoRellich.lean

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangianCore_symmetricOn
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

theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangianCore_symmetricOn : SymmetricOn L.D (lagrangianCore L) := by sorry
