-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_discounted_finite_clock_continuous_coefficients_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_continuous_coefficients_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:15:49.695189+00:00
-- url     : https://prove2.me/theorems/c5eee410-1659-4bfd-adbf-771f3ba5b53b
-- title:
--   Original Gaussian plus epsilon physical drift coefficients are jointly discounted L1 on finite interior clock
-- statement:
--   The exact original spectrally negative Levy generator Gaussian sigma²/2 correction and physical epsilon drift (c minus the finite negative-annulus mark first moment) form a jointly integrable discounted finite-variation drift on any finite measurable observation clock whose reserve is in a compact strict C² interior band. The uniform Gaussian Hessian and derivative-plus-annulus physical drift bounds are derived from source hypotheses, with measurability of both derivatives explicitly required. This does not construct stochastic integrals or extend to zero/cap.
-- source:
--   Source Gaussian compact Hessian bound fce33e7b-de46-4ff0-aeda-ad74bd21b08a; original Levy physical drift bound 36c9748f-402f-4058-81c1-32e098911d4d; finite-clock drift L1 624da4e4-9ff2-4552-822c-f81bb07a1fdf pending.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_discounted_finite_clock_physical_drift_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_continuous_coefficients_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (clock : T → ℝ≥0) (w : ℝ → ℝ) (q : ℝ)
    (hder : Measurable (fun t => deriv w (R t)))
    (hhess : Measurable (fun t => iteratedDeriv 2 w (R t)))
    (hclock : Measurable clock)
    (hq : 0 ≤ q) (A : Set T) (hA : MeasurableSet A)
    (C : ℝ) (Cap : ℝ≥0∞) (u v ε : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hwCap : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap})
    (hu : 0 < u) (hv : v < C) (hε : 0 < ε)
    (hBand : Icc u v ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap})
    (hcap : ∀ t ∈ A, R t ∈ Icc u v) :
    Integrable (A.indicator (fun t : T =>
      Real.exp (-(q * (clock t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (R t) +
         (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w (R t)))) μ := by sorry
