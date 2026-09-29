-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystem_qgR2_sirk_crouzeix_domain
-- name    : BookProof.ChapterSirkPerSystem.qgR2_sirk_crouzeix_domain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:40:53.376238+00:00
-- url     : https://prove2.me/theorems/e9f9cebc-67c4-482f-a55f-7345ff266549
-- title:
--   (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ) {γ : ℂ} (hγ : γ.im ≠ 0) : ∃ (Dom : Submodule ℂ L2Nat) (A : Dom →ₗ[ℂ] L2Nat) (X : L2Nat →L[ℂ] L2Nat), IsSelfAdjointExtension (qgR2ModeHamiltonian a b M alpha...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkPerSystem.qgR2_sirk_crouzeix_domain` (module `BookProof.ChapterSirkPerSystem`), source chapter `BookProof/ChapterChapterSirkPerSystem.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkPerSystem.lean

-- Generated from ChapterSirkPerSystem.lean — theorem BookProof.ChapterSirkPerSystem.qgR2_sirk_crouzeix_domain
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

theorem BookProof.ChapterSirkPerSystem.qgR2_sirk_crouzeix_domain (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)
    {γ : ℂ} (hγ : γ.im ≠ 0) :
    ∃ (Dom : Submodule ℂ L2Nat) (A : Dom →ₗ[ℂ] L2Nat) (X : L2Nat →L[ℂ] L2Nat),
      IsSelfAdjointExtension (qgR2ModeHamiltonian a b M alpha Rc) A ∧
      IsShiftInvertC A γ X ∧ ‖X‖ ≤ |γ.im|⁻¹ ∧
      numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ ∧
      ∀ (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2Nat), (∀ x, ‖V x‖ = ‖x‖) →
        convexHull ℝ (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ := by sorry
