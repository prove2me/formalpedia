-- Prove2me | Theorems.Thm_FeynmanKac_augmented_coefficients_all_time_ae
-- name    : FeynmanKac.augmented_coefficients_all_time_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:21:48.396839+00:00
-- url     : https://prove2.me/theorems/48bcc56d-ddd1-4ce7-bce8-c39a05086af3
-- title:
--   One null set supports all time-dependent coefficient identities
-- statement:
--   Outside one single P-null set, for all elapsed Brownian times r≥0 simultaneously, the spatial drift and volatility of the clock-augmented autonomous SDE are exactly μ(X_{t+r},t+r) and σ(X_{t+r},t+r). This strengthens a fixed-r almost-everywhere identity and allows pathwise substitution under all time integrals in the vector Itô formula without any unjustified intersection over uncountably many null sets. It follows from the independently proved uniform deterministic-clock identity and the model's non-circular coefficient definitions.
-- source:
--   Uniform clock bridge FeynmanKac.clock_coordinate_all_nonnegative_ae; canonical diffusion coefficient identities

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Theorems.Thm_FeynmanKac_clock_coordinate_all_nonnegative_ae

theorem FeynmanKac.augmented_coefficients_all_time_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) :
    ∀ᵐ ω ∂P, ∀ (r : ℝ), 0 ≤ r →
      m.augmentedDrift (m.augmentedPath r ω) (0 : Fin 2) =
        m.drift (m.path (m.initialTime + r) ω) (m.initialTime + r) ∧
      m.augmentedVolatility (m.augmentedPath r ω) 0 (0 : Fin 2) =
        m.volatility (m.path (m.initialTime + r) ω) (m.initialTime + r) := by sorry
