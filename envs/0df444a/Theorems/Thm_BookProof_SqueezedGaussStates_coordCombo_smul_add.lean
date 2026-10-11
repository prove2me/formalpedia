-- Prove2me | Theorems.Thm_BookProof_SqueezedGaussStates_coordCombo_smul_add
-- name    : BookProof.SqueezedGaussStates.coordCombo_smul_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:24:20.556483+00:00
-- url     : https://prove2.me/theorems/ff5de2f1-d475-4880-886d-6c72c834eea4
-- title:
--   `BookProof.SqueezedGaussStates.coordCombo_smul_add` (i : Fin d) (c₁ c₂ : ℕ → ℝ) (α γ : ℝ) (p K : ℕ) : ((α : ℝ) : ℂ) • coordCombo i c₁ p K + ((γ : ℝ) : ℂ) •...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqueezedGaussStates`.
--
--   `BookProof.SqueezedGaussStates.coordCombo_smul_add` (i : Fin d) (c₁ c₂ : ℕ → ℝ) (α γ : ℝ) (p K : ℕ) : ((α : ℝ) : ℂ) • coordCombo i c₁ p K + ((γ : ℝ) : ℂ) • coordCombo i c₂ p K = coordCombo i (fun k => α * c₁ k + γ * c₂ k) p K
--
--   Formalization note: Lean 4 identifier `BookProof.SqueezedGaussStates.coordCombo_smul_add`.

-- Generated from ChapterSqueezedGaussStates.lean — theorem BookProof.SqueezedGaussStates.coordCombo_smul_add
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.GaussCoordCombo
open BookProof.HermiteProductCore
open BookProof.SqueezedGaussStates



open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

theorem BookProof.SqueezedGaussStates.coordCombo_smul_add (i : Fin d) (c₁ c₂ : ℕ → ℝ) (α γ : ℝ) (p K : ℕ) :
    ((α : ℝ) : ℂ) • coordCombo i c₁ p K + ((γ : ℝ) : ℂ) • coordCombo i c₂ p K
      = coordCombo i (fun k => α * c₁ k + γ * c₂ k) p K := by sorry
