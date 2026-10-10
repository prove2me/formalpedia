-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_integral_moll_eq_self_of_analytic
-- name    : BookProof.RadialMollifier.integral_moll_eq_self_of_analytic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:02:39.004985+00:00
-- url     : https://prove2.me/theorems/b13cbf3a-3327-4631-a4a2-a7d4e6e8d2d3
-- title:
--   `BookProof.RadialMollifier.integral_moll_eq_self_of_analytic` {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hh : DifferentiableOn ℂ h s) (hcont : Continuous h) {δ : ℝ} (hδ : 0 < δ) {z :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.integral_moll_eq_self_of_analytic` {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hh : DifferentiableOn ℂ h s) (hcont : Continuous h) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : closedBall z δ ⊆ s) : ∫ w : ℂ, (moll δ (z - w) : ℂ) * h w = h z
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.integral_moll_eq_self_of_analytic`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.integral_moll_eq_self_of_analytic
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.integral_moll_eq_self_of_analytic {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s)
    (hh : DifferentiableOn ℂ h s) (hcont : Continuous h) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : closedBall z δ ⊆ s) :
    ∫ w : ℂ, (moll δ (z - w) : ℂ) * h w = h z := by sorry
