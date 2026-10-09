-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeWeylResidual_weyl_surface_preserved_by_remnant
-- name    : BookProof.ChapterGaugeWeylResidual.weyl_surface_preserved_by_remnant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:17:50.6155+00:00
-- url     : https://prove2.me/theorems/6a43e84d-2a53-4d3e-8242-fcb4a61a20ee
-- title:
--   `BookProof.ChapterGaugeWeylResidual.weyl_surface_preserved_by_remnant` (θ A0 : ℝ → ℝ → ℝ) (hθ : ∀ x, Differentiable ℝ (fun s => θ s x)) (hti : TimeIndependent θ) (hA0 : A0 = fun _
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeWeylResidual`.
--
--   `BookProof.ChapterGaugeWeylResidual.weyl_surface_preserved_by_remnant` (θ A0 : ℝ → ℝ → ℝ) (hθ : ∀ x, Differentiable ℝ (fun s => θ s x)) (hti : TimeIndependent θ) (hA0 : A0 = fun _ _ => 0) : gaugeA0 θ A0 = fun _ _ => 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeWeylResidual.weyl_surface_preserved_by_remnant`.

-- Generated from ChapterGaugeWeylResidual.lean — theorem BookProof.ChapterGaugeWeylResidual.weyl_surface_preserved_by_remnant
import Mathlib
import Definitions.Def_ChapterGaugeWeylResidual
open BookProof.ChapterGaugeWeylResidual

theorem BookProof.ChapterGaugeWeylResidual.weyl_surface_preserved_by_remnant (θ A0 : ℝ → ℝ → ℝ)
    (hθ : ∀ x, Differentiable ℝ (fun s => θ s x)) (hti : TimeIndependent θ)
    (hA0 : A0 = fun _ _ => 0) :
    gaugeA0 θ A0 = fun _ _ => 0 := by sorry
