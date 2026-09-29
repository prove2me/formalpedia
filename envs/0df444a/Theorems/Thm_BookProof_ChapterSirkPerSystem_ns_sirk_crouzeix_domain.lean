-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystem_ns_sirk_crouzeix_domain
-- name    : BookProof.ChapterSirkPerSystem.ns_sirk_crouzeix_domain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:36:51.420431+00:00
-- url     : https://prove2.me/theorems/c7f0ce31-9bf7-4863-91d1-7f4eb6e7695e
-- title:
--   (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (b : HilbertBasis ℕ ℂ (L2I Vel)) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) : ∃ (Dom : Submodule ℂ (L2I Vel)) (G : Dom →ₗ[ℂ] L2I Vel) (X : ℕ → L2I Vel →L[ℂ]...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkPerSystem.ns_sirk_crouzeix_domain` (module `BookProof.ChapterSirkPerSystem`), source chapter `BookProof/ChapterChapterSirkPerSystem.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkPerSystem.lean

-- Generated from ChapterSirkPerSystem.lean — theorem BookProof.ChapterSirkPerSystem.ns_sirk_crouzeix_domain
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

theorem BookProof.ChapterSirkPerSystem.ns_sirk_crouzeix_domain (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
    (b : HilbertBasis ℕ ℂ (L2I Vel)) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ (L2I Vel)) (G : Dom →ₗ[ℂ] L2I Vel)
      (X : ℕ → L2I Vel →L[ℂ] L2I Vel),
      IsSelfAdjointExtension (velCore A c) G ∧
      (∀ j, IsShiftInvertC G (γ j) (X j)) ∧
      (∀ j, numRange (X j) ⊆ Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹) ∧
      ∀ (j m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2I Vel), (∀ x, ‖V x‖ = ‖x‖) →
        convexHull ℝ (numRange (compress V (X j)))
          ⊆ Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹ := by sorry
