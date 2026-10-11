-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_weak_cauchyRiemann_iff_ae_eq_analytic
-- name    : BookProof.WeylCauchyRiemann.weak_cauchyRiemann_iff_ae_eq_analytic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T17:36:06.289983+00:00
-- url     : https://prove2.me/theorems/e2460acd-4216-4303-a89e-e4899ed49ffe
-- title:
--   `BookProof.WeylCauchyRiemann.weak_cauchyRiemann_iff_ae_eq_analytic` {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : LocallyIntegrableOn f U) : WeakCauchyRiemannOn f U ↔ ∃ g : ℂ → ℂ,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.weak_cauchyRiemann_iff_ae_eq_analytic` {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : LocallyIntegrableOn f U) : WeakCauchyRiemannOn f U ↔ ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ ∀ᵐ z : ℂ, z ∈ U → f z = g z
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.weak_cauchyRiemann_iff_ae_eq_analytic`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.weak_cauchyRiemann_iff_ae_eq_analytic
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.weak_cauchyRiemann_iff_ae_eq_analytic {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U) :
    WeakCauchyRiemannOn f U ↔ ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ ∀ᵐ z : ℂ, z ∈ U → f z = g z := by sorry
