-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystem_nsDiff_sirk_crouzeix_domain
-- name    : BookProof.ChapterSirkPerSystem.nsDiff_sirk_crouzeix_domain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T02:55:49.89335+00:00
-- url     : https://prove2.me/theorems/9c077944-d5fc-4dd8-bcf2-dc67778094a5
-- title:
--   (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) {γ : ℂ} (hγ : γ.im ≠ 0) : ∃ (Dom : Submodule ℂ (L2d 3)) (G : Dom →ₗ[ℂ] L2d 3) (X : L2d 3 →L[ℂ] L2d 3), IsSelfAdjointExtension ((polyGaussCore (d
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkPerSystem.nsDiff_sirk_crouzeix_domain` (module `BookProof.ChapterSirkPerSystem`), source chapter `BookProof/ChapterChapterSirkPerSystem.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkPerSystem.lean

-- Generated from ChapterSirkPerSystem.lean — theorem BookProof.ChapterSirkPerSystem.nsDiff_sirk_crouzeix_domain
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

theorem BookProof.ChapterSirkPerSystem.nsDiff_sirk_crouzeix_domain (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
    {γ : ℂ} (hγ : γ.im ≠ 0) :
    ∃ (Dom : Submodule ℂ (L2d 3)) (G : Dom →ₗ[ℂ] L2d 3) (X : L2d 3 →L[ℂ] L2d 3),
      IsSelfAdjointExtension ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) G ∧
      IsShiftInvertC G γ X ∧ ‖X‖ ≤ |γ.im|⁻¹ ∧
      numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ ∧
      ∀ (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2d 3), (∀ x, ‖V x‖ = ‖x‖) →
        convexHull ℝ (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ := by sorry
