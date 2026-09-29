-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffHashimoto_nsDiffH_hashimoto_selects
-- name    : BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_hashimoto_selects
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T07:51:51.217584+00:00
-- url     : https://prove2.me/theorems/dda0ac54-04aa-445f-bfd5-8b3230d6c85e
-- title:
--   The Lean 4 theorem `nsDiffH_hashimoto_selects` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsDiffH_hashimoto_selects` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffHashimoto.lean

-- Generated from ChapterNavierStokesDiffHashimoto.lean — theorem BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_hashimoto_selects
import Mathlib
import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Definitions.Def_ChapterHashimotoComplexShifts
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

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.

theorem BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_hashimoto_selects (b : HilbertBasis ℕ ℂ (L2d 3)) (γ : ℕ → ℂ)
    (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ (L2d 3)) (G : Dom →ₗ[ℂ] L2d 3) (X : ℕ → L2d 3 →L[ℂ] L2d 3),
      IsSelfAdjointExtension ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) G ∧
      (∀ j, IsShiftInvertC G (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : L2d 3 →ₗ[ℂ] L2d 3))) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ (L2d 3) - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) b n u) atTop (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ (L2d 3)) (G' : Dom' →ₗ[ℂ] L2d 3),
        IsShiftInvertC G' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : L2d 3) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
          G' ⟨x, hx'⟩ = G ⟨x, hx⟩) := by sorry
