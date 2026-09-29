-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_lagrangian_selfAdjoint_extension
-- name    : BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:11:21.984932+00:00
-- url     : https://prove2.me/theorems/a02f2a8a-ee98-4796-8b6c-76de3f06e71e
-- title:
--   The Lean 4 theorem `lagrangian_selfAdjoint_extension` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `lagrangian_selfAdjoint_extension` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianKatoRellich.lean

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension
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

theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension
    (hesa : EssentiallySelfAdjointOn L.D (lagrangianCore L)) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsSelfAdjointExtension (lagrangianCore L) A := by sorry
