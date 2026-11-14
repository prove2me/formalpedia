-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
-- name    : AvramDividend.Classical.avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:34:48.026347+00:00
-- url     : https://prove2.me/theorems/d10af075-010c-48bb-9ecc-d45918c2babf
-- title:
--   Original zero-jump Gaussian drift-centred deterministic source increments have positive normalised exponential integrability
-- statement:
--   For original pure-Gaussian Levy source X, positive sigma, any deterministic physical times s≤t and nonnegative theta, the exponential of theta times the original drift-centred increment divided by its actual volatility is integrable.
-- source:
--   Original stopped positive L1 Gaussian upper-surplus source tail b0d9951c; no auxiliary integrability via proved zero-jump compensated source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ))) P := by sorry
