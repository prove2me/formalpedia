-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffHashimoto_nsDiffH_selfAdjoint_extension_unique
-- name    : BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_selfAdjoint_extension_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:51:25.885472+00:00
-- url     : https://prove2.me/theorems/e2ab99c2-5f6c-4b62-9896-2ba023414afa
-- title:
--   The Lean 4 theorem `nsDiffH_selfAdjoint_extension_unique` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsDiffH_selfAdjoint_extension_unique` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffHashimoto.lean

-- Generated from ChapterNavierStokesDiffHashimoto.lean — theorem BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_selfAdjoint_extension_unique
import Mathlib
import Definitions.Def_ChapterNavierStokesDiffHashimoto
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiffHashimoto







open Filter Topology



open MvPolynomial
open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteRelative
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_selfAdjoint_extension_unique {Dom₁ Dom₂ : Submodule ℂ (L2d 3)}
    {G₁ : Dom₁ →ₗ[ℂ] L2d 3} {G₂ : Dom₂ →ₗ[ℂ] L2d 3}
    (h₁ : IsSelfAdjointExtension ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) G₁)
    (h₂ : IsSelfAdjointExtension ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) G₂) :
    Dom₁ = Dom₂ ∧ ∀ (x : L2d 3) (h : x ∈ Dom₁) (h' : x ∈ Dom₂), G₁ ⟨x, h⟩ = G₂ ⟨x, h'⟩ := by sorry
