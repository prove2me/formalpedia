-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_analyticOn
-- name    : BookProof.WeylCauchyRiemann.mollify_analyticOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T17:13:51.503381+00:00
-- url     : https://prove2.me/theorems/5025e5b6-4ae5-46a3-b40b-24d3cafb070a
-- title:
--   `BookProof.WeylCauchyRiemann.mollify_analyticOn` {f : ℂ → ℂ} {U : Set ℂ} (hf : LocallyIntegrableOn f U) (hCR : WeakCauchyRiemannOn f U) {c : ℂ} {R r δ : ℝ} (hδ : 0 < δ) (hr : 0 < r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.mollify_analyticOn` {f : ℂ → ℂ} {U : Set ℂ} (hf : LocallyIntegrableOn f U) (hCR : WeakCauchyRiemannOn f U) {c : ℂ} {R r δ : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hrR : r + δ ≤ R) (hKU : closedBall c R ⊆ U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hsupp : Function.support χ ⊆ ball (0 : ℂ) δ) : AnalyticOn ℂ (mollify ((closedBall c R).indicator f) χ) (ball c r)
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.mollify_analyticOn`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.mollify_analyticOn
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.mollify_analyticOn {f : ℂ → ℂ} {U : Set ℂ}
    (hf : LocallyIntegrableOn f U) (hCR : WeakCauchyRiemannOn f U)
    {c : ℂ} {R r δ : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hrR : r + δ ≤ R)
    (hKU : closedBall c R ⊆ U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hsupp : Function.support χ ⊆ ball (0 : ℂ) δ) :
    AnalyticOn ℂ (mollify ((closedBall c R).indicator f) χ) (ball c r) := by sorry
