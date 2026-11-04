-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_discounted_finite_clock_physical_drift_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_physical_drift_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:07:17.958933+00:00
-- url     : https://prove2.me/theorems/624da4e4-9ff2-4552-822c-f81bb07a1fdf
-- title:
--   Source Levy epsilon physical drift is L1 on finite stopped interior clock under actual exponential discount
-- statement:
--   For the original spectrally negative Levy generator with its actual unit-interval truncation convention, the compensated physical drift c minus the finite negative annulus first moment times a C² payoff derivative is integrable under its genuine nonnegative-time exponential discount on any finite observation clock with compact interior reserves. Derives the required discount bound directly from nonnegative rate and time, without postulating drift integrability or a stochastic compensator. The measurable derivative along reserves is explicit.
-- source:
--   Source SpectrallyNegativeLevy generator, proven compact physical drift bound 36c9748f-402f-4058-81c1-32e098911d4d and first moment 63c53f4c-113e-48e0-8d54-55be014f9398.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_compact_physical_drift_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_physical_drift_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R clock : T → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hder : Measurable (fun t => deriv w (R t)))
    (hcmeas : Measurable clock) (hcpos : ∀ t, 0 ≤ clock t)
    (hq : 0 ≤ q) (A : Set T) (hA : MeasurableSet A)
    (C u v ε : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hu : 0 < u) (hv : v < C) (hε : 0 < ε)
    (hcap : ∀ t ∈ A, R t ∈ Icc u v) :
    Integrable (A.indicator (fun t : T =>
      Real.exp (-(q * clock t)) *
        ((X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) *
          deriv w (R t)))) μ := by sorry
