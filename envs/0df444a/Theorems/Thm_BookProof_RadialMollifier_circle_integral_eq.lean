-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_circle_integral_eq
-- name    : BookProof.RadialMollifier.circle_integral_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:02:30.060924+00:00
-- url     : https://prove2.me/theorems/30e7b81b-d0f4-4179-8740-2806aff302d9
-- title:
--   `BookProof.RadialMollifier.circle_integral_eq` {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hh : DifferentiableOn ℂ h s) {z : ℂ} {r : ℝ} (hr : 0 < r) (hsub : closedBall z r ⊆ s) : ∫ θ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.circle_integral_eq` {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hh : DifferentiableOn ℂ h s) {z : ℂ} {r : ℝ} (hr : 0 < r) (hsub : closedBall z r ⊆ s) : ∫ θ in (-π)..π, h (z - (r : ℂ) * Complex.exp (θ * Complex.I)) = ((2 * π : ℝ) : ℂ) * h z
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.circle_integral_eq`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.circle_integral_eq
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.circle_integral_eq {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hh : DifferentiableOn ℂ h s)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hsub : closedBall z r ⊆ s) :
    ∫ θ in (-π)..π, h (z - (r : ℂ) * Complex.exp (θ * Complex.I)) = ((2 * π : ℝ) : ℂ) * h z := by sorry
