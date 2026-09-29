-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_lagrangian_selfAdjoint_extension_unique
-- name    : BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:54:42.313525+00:00
-- url     : https://prove2.me/theorems/5c977681-f3e6-4fd3-bc62-65890212ca18
-- title:
--   The Lean 4 theorem `lagrangian_selfAdjoint_extension_unique` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `lagrangian_selfAdjoint_extension_unique` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianKatoRellich.lean

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension_unique
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

theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension_unique
    (hesa : EssentiallySelfAdjointOn L.D (lagrangianCore L))
    {Dom₁ Dom₂ : Submodule ℂ F} {A₁ : Dom₁ →ₗ[ℂ] F} {A₂ : Dom₂ →ₗ[ℂ] F}
    (h₁ : IsSelfAdjointExtension (lagrangianCore L) A₁)
    (h₂ : IsSelfAdjointExtension (lagrangianCore L) A₂) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (h : x ∈ Dom₁) (h' : x ∈ Dom₂), A₁ ⟨x, h⟩ = A₂ ⟨x, h'⟩ := by sorry
