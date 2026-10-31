-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_curvature_zeroext_weighted
-- name    : AvramDividend.Classical.avram_wave3_05_source_gaussian_curvature_zeroext_weighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:50:33.345818+00:00
-- url     : https://prove2.me/theorems/9f9b8a9f-6659-4a06-bcec-1f96ebbc0f3c
-- title:
--   Source Gaussian W double-prime zero-extension has eventual global exponential L1 mass
-- statement:
--   For the original spectrally negative Lévy q-scale with strictly positive Gaussian coefficient, there is a sufficiently large exponential discount θ such that the actual second derivative W'' cut off to positive reserves is globally measurable and exponentially weighted integrable on all real reserves, with continuity on positive reserves. This avoids assuming an unsupported full-line W'' moment or differentiability of the zero extension at zero.
-- source:
--   Accepted Gaussian C² theorem 4c4d5e79, accepted eventual W'' theorem bb2c6978, private remote Lean proof candidate zero-extension 30 October 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_Wsecond_weighted

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_05_source_gaussian_curvature_zeroext_weighted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      let F : ℝ → ℝ :=
        (Ioi (0 : ℝ)).piecewise (deriv (deriv W)) (fun _ => 0)
      Measurable F ∧ ContinuousOn F (Ioi (0 : ℝ)) ∧
        Integrable (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume := by sorry
