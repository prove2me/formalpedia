-- Prove2me | Theorems.Thm_BookProof_ChapterSirkPerSystem_qgR2_shiftInvert_selects
-- name    : BookProof.ChapterSirkPerSystem.qgR2_shiftInvert_selects
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:37:37.195286+00:00
-- url     : https://prove2.me/theorems/58a8e767-0fdf-49dc-93a1-f9d61033a1dd
-- title:
--   (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ) {γ : ℂ} (hγ : γ.im ≠ 0) : ∃ (Dom : Submodule ℂ L2Nat) (A : Dom →ₗ[ℂ] L2Nat) (X : L2Nat →L[ℂ] L2Nat), IsSelfAdjointExtension (qgR2ModeHamiltonian a b M alpha...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkPerSystem.qgR2_shiftInvert_selects` (module `BookProof.ChapterSirkPerSystem`), source chapter `BookProof/ChapterChapterSirkPerSystem.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkPerSystem.lean

-- Generated from ChapterSirkPerSystem.lean — theorem BookProof.ChapterSirkPerSystem.qgR2_shiftInvert_selects
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

theorem BookProof.ChapterSirkPerSystem.qgR2_shiftInvert_selects (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)
    {γ : ℂ} (hγ : γ.im ≠ 0) :
    ∃ (Dom : Submodule ℂ L2Nat) (A : Dom →ₗ[ℂ] L2Nat) (X : L2Nat →L[ℂ] L2Nat),
      IsSelfAdjointExtension (qgR2ModeHamiltonian a b M alpha Rc) A ∧
      IsShiftInvertC A γ X ∧ ‖X‖ ≤ |γ.im|⁻¹ := by sorry
