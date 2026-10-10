-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_polar_radial
-- name    : BookProof.RadialMollifier.polar_radial
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:02:07.692973+00:00
-- url     : https://prove2.me/theorems/267d6ed2-bcb2-4cfb-8d43-567bfa66ef33
-- title:
--   `BookProof.RadialMollifier.polar_radial` {δ : ℝ} (hδ : 0 < δ) (G : ℂ → ℂ) (hG : Continuous G) : ∫ u : ℂ, (moll δ u : ℂ) * G u = ∫ r in Ioi (0 : ℝ), ((r * moll δ r : ℝ)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.polar_radial` {δ : ℝ} (hδ : 0 < δ) (G : ℂ → ℂ) (hG : Continuous G) : ∫ u : ℂ, (moll δ u : ℂ) * G u = ∫ r in Ioi (0 : ℝ), ((r * moll δ r : ℝ) : ℂ) * ∫ θ in (-π)..π, G (Complex.polarCoord.symm (r, θ))
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.polar_radial`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.polar_radial
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.polar_radial {δ : ℝ} (hδ : 0 < δ) (G : ℂ → ℂ) (hG : Continuous G) :
    ∫ u : ℂ, (moll δ u : ℂ) * G u
      = ∫ r in Ioi (0 : ℝ), ((r * moll δ r : ℝ) : ℂ) *
          ∫ θ in (-π)..π, G (Complex.polarCoord.symm (r, θ)) := by sorry
