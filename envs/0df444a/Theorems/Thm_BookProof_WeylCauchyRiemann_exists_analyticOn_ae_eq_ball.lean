-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_exists_analyticOn_ae_eq_ball
-- name    : BookProof.WeylCauchyRiemann.exists_analyticOn_ae_eq_ball
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:34:17.368663+00:00
-- url     : https://prove2.me/theorems/07a49b6f-2610-455c-b001-dfa5c040ef22
-- title:
--   `BookProof.WeylCauchyRiemann.exists_analyticOn_ae_eq_ball` {f : ℂ → ℂ} {U : Set ℂ} (hf : LocallyIntegrableOn f U) (hCR : WeakCauchyRiemannOn f U) {c : ℂ} {R : ℝ} (hR : 0 < R) (hKU
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.exists_analyticOn_ae_eq_ball` {f : ℂ → ℂ} {U : Set ℂ} (hf : LocallyIntegrableOn f U) (hCR : WeakCauchyRiemannOn f U) {c : ℂ} {R : ℝ} (hR : 0 < R) (hKU : closedBall c R ⊆ U) : ∃ g : ℂ → ℂ, AnalyticOn ℂ g (ball c (R / 4)) ∧ ∀ᵐ z : ℂ, z ∈ ball c (R / 4) → f z = g z
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.exists_analyticOn_ae_eq_ball`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.exists_analyticOn_ae_eq_ball
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.exists_analyticOn_ae_eq_ball {f : ℂ → ℂ} {U : Set ℂ}
    (hf : LocallyIntegrableOn f U) (hCR : WeakCauchyRiemannOn f U)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hKU : closedBall c R ⊆ U) :
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g (ball c (R / 4)) ∧
      ∀ᵐ z : ℂ, z ∈ ball c (R / 4) → f z = g z := by sorry
