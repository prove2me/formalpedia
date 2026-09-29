-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_lagrangian_hashimoto_selects
-- name    : BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_hashimoto_selects
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:23:26.07899+00:00
-- url     : https://prove2.me/theorems/04e6369e-c70c-4e67-b958-907d55109ac8
-- title:
--   The Lean 4 theorem `lagrangian_hashimoto_selects` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `lagrangian_hashimoto_selects` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianKatoRellich.lean

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_hashimoto_selects
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich
open Filter Topology
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)


























variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (L : LagrangianFullData F)

theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_hashimoto_selects
    (hesa : EssentiallySelfAdjointOn L.D (lagrangianCore L))
    (bas : HilbertBasis ℕ ℂ F) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (X : ℕ → F →L[ℂ] F),
      IsSelfAdjointExtension (lagrangianCore L) A ∧
      (∀ j, IsShiftInvertC A (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : F →ₗ[ℂ] F))) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ F - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) bas n u) atTop (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvertC A' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by sorry
