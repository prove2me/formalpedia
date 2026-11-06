-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianEsa_ymAbelian_hashimoto_selects
-- name    : BookProof.YangMillsAbelianEsa.ymAbelian_hashimoto_selects
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-05T19:46:55.564406+00:00
-- url     : https://prove2.me/theorems/c74c94a5-ca21-4cd8-a6a8-781b27196c3f
-- title:
--   `BookProof.YangMillsAbelianEsa.ymAbelian_hashimoto_selects` (b : HilbertBasis ℕ ℂ (L2d 99)) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) : ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianEsa`.
--
--   `BookProof.YangMillsAbelianEsa.ymAbelian_hashimoto_selects` (b : HilbertBasis ℕ ℂ (L2d 99)) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) : ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (X : ℕ → L2d 99 →L[ℂ] L2d 99), IsSelfAdjointExtension (ymHamiltonian (coreRepPoly 99) 0) A ∧ (∀ j, IsShiftInvertC A (γ j) (X j)) ∧ (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧ (∀ j, Dom = LinearMap.range ((X j : L2d 99 →ₗ[ℂ] L2d 99))) ∧ (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧ (∀ j k, X j ∘L X k = X k ∘L X j) ∧ (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ (L2d 99) - (γ m - γ j) • X m) = X m) ∧ (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧ (∀ j u, Filter.Tendsto (fun n : ℕ => galerkinCompression (X j) b n u) Filter.atTop (nhds (X j u))) ∧ (∀ j (Dom' : Submodule ℂ (L2d 99)) (A' : Dom' →ₗ[ℂ] L2d 99), IsShiftInvertC A' (γ j) (X j) → Dom' = Dom ∧ ∀ (x : L2d 99) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩)
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianEsa.ymAbelian_hashimoto_selects`.

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.ymAbelian_hashimoto_selects
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterYangMillsAbelianEsa
open BookProof.EsaClosure
open BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite
open BookProof.YangMillsAbelianEsa



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

theorem BookProof.YangMillsAbelianEsa.ymAbelian_hashimoto_selects (b : HilbertBasis ℕ ℂ (L2d 99)) (γ : ℕ → ℂ)
    (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (X : ℕ → L2d 99 →L[ℂ] L2d 99),
      IsSelfAdjointExtension (ymHamiltonian (coreRepPoly 99) 0) A ∧
      (∀ j, IsShiftInvertC A (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : L2d 99 →ₗ[ℂ] L2d 99))) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ (L2d 99) - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Filter.Tendsto (fun n : ℕ => galerkinCompression (X j) b n u) Filter.atTop
        (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ (L2d 99)) (A' : Dom' →ₗ[ℂ] L2d 99),
        IsShiftInvertC A' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : L2d 99) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
          A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by sorry
