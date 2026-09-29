-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystem_ym_sirk_crouzeix_domain
-- name    : BookProof.ChapterSirkPerSystem.ym_sirk_crouzeix_domain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:38:22.126555+00:00
-- url     : https://prove2.me/theorems/b5d73f63-a7da-4a2e-aa1f-482008c958b5
-- title:
--   (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {γ : ℝ} (hγ : 0 < γ) : ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (R : L2d 99 →L[ℂ] L2d 99), IsPositiveSelfAdjointExtension (ym...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkPerSystem.ym_sirk_crouzeix_domain` (module `BookProof.ChapterSirkPerSystem`), source chapter `BookProof/ChapterChapterSirkPerSystem.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkPerSystem.lean

-- Generated from ChapterSirkPerSystem.lean — theorem BookProof.ChapterSirkPerSystem.ym_sirk_crouzeix_domain
import Mathlib
import Definitions.Def_ChapterSirkPerSystem
open BookProof.ChapterSirkPerSystem









noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH9 BookProof.ChapterSirkSpectralGeometry
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.EsaClosure
open BookProof.YangMillsFriedrichs BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.Starobinsky
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.NSHashimoto
open BookProof.NavierStokesFlow.DiffHashimoto BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.LagrangianEsa BookProof.NavierStokesFlow.LagrangianKatoRellich

theorem BookProof.ChapterSirkPerSystem.ym_sirk_crouzeix_domain (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (R : L2d 99 →L[ℂ] L2d 99),
      IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepBasis e) fabc) A ∧
        IsShiftInvert A γ R ∧ IsSelfAdjoint R ∧
        numRange R ⊆ realSegment 0 γ⁻¹ ∧
        ∀ (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2d 99),
          (∀ x, ‖V x‖ = ‖x‖) →
            convexHull ℝ (numRange (compress V R)) ⊆ realSegment 0 γ⁻¹ := by sorry
