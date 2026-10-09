-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeWeylResidual_remnant_moves_every_configuration
-- name    : BookProof.ChapterGaugeWeylResidual.remnant_moves_every_configuration
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:17:51.407978+00:00
-- url     : https://prove2.me/theorems/4302dd6a-0668-4af5-9840-741335ee7c27
-- title:
--   `BookProof.ChapterGaugeWeylResidual.remnant_moves_every_configuration` : ∃ θ : ℝ → ℝ → ℝ, TimeIndependent θ ∧ (∀ t x, dt θ t x = 0) ∧ (∀ t x, dx θ t x = 1) ∧ ∀ A1 :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeWeylResidual`.
--
--   `BookProof.ChapterGaugeWeylResidual.remnant_moves_every_configuration` : ∃ θ : ℝ → ℝ → ℝ, TimeIndependent θ ∧ (∀ t x, dt θ t x = 0) ∧ (∀ t x, dx θ t x = 1) ∧ ∀ A1 : ℝ → ℝ → ℝ, gaugeA1 θ A1 ≠ A1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeWeylResidual.remnant_moves_every_configuration`.

-- Generated from ChapterGaugeWeylResidual.lean — theorem BookProof.ChapterGaugeWeylResidual.remnant_moves_every_configuration
import Mathlib
import Definitions.Def_ChapterGaugeWeylResidual
open BookProof.ChapterGaugeWeylResidual

theorem BookProof.ChapterGaugeWeylResidual.remnant_moves_every_configuration :
    ∃ θ : ℝ → ℝ → ℝ, TimeIndependent θ ∧ (∀ t x, dt θ t x = 0) ∧
      (∀ t x, dx θ t x = 1) ∧ ∀ A1 : ℝ → ℝ → ℝ, gaugeA1 θ A1 ≠ A1 := by sorry
