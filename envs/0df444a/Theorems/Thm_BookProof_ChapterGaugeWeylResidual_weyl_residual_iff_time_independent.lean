-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeWeylResidual_weyl_residual_iff_time_independent
-- name    : BookProof.ChapterGaugeWeylResidual.weyl_residual_iff_time_independent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:17:34.869279+00:00
-- url     : https://prove2.me/theorems/ca91a304-7075-4c33-944e-d235e0302345
-- title:
--   `BookProof.ChapterGaugeWeylResidual.weyl_residual_iff_time_independent` (θ : ℝ → ℝ → ℝ) (hθ : ∀ x, Differentiable ℝ (fun s => θ s x)) : (∀ t x, dt θ t x = 0) ↔ TimeIndependent θ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeWeylResidual`.
--
--   `BookProof.ChapterGaugeWeylResidual.weyl_residual_iff_time_independent` (θ : ℝ → ℝ → ℝ) (hθ : ∀ x, Differentiable ℝ (fun s => θ s x)) : (∀ t x, dt θ t x = 0) ↔ TimeIndependent θ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeWeylResidual.weyl_residual_iff_time_independent`.

-- Generated from ChapterGaugeWeylResidual.lean — theorem BookProof.ChapterGaugeWeylResidual.weyl_residual_iff_time_independent
import Mathlib
import Definitions.Def_ChapterGaugeWeylResidual
open BookProof.ChapterGaugeWeylResidual

theorem BookProof.ChapterGaugeWeylResidual.weyl_residual_iff_time_independent (θ : ℝ → ℝ → ℝ)
    (hθ : ∀ x, Differentiable ℝ (fun s => θ s x)) :
    (∀ t x, dt θ t x = 0) ↔ TimeIndependent θ := by sorry
