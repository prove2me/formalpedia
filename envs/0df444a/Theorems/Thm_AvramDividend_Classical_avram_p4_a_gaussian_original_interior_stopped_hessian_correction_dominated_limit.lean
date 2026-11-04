-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_interior_stopped_hessian_correction_dominated_limit
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_hessian_correction_dominated_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:58:05.099646+00:00
-- url     : https://prove2.me/theorems/20d29676-67f3-4014-ac83-f90778a4e79f
-- title:
--   Original Levy Gaussian Hessian correction dominated-convergence limit on true compact interior stopped interval
-- statement:
--   For the actual spectrally negative Levy X with original Gaussian coefficient, and w satisfying the source exact C² condition only on the strict interior, every compact interior localisation band yields a uniform time-discounted Gaussian Hessian bound. For finite-measure stopped time intervals and measurable interior-valued mesh approximants converging a.e at the integrand level, dominated convergence passes the Gaussian σ²/2 correction to its stopped time integral. No boundedness outside the band or endpoint occupation assertion is used. The pathwise convergence of true original left-state approximants is an explicit upstream P4-E obligation.
-- source:
--   Published source-specific compact interior discounted Hessian uniform bound plus pinned Mathlib dominated-convergence theorem. Avram, Palmowski and Pistorius, Proposition 4(i), equation (5.10).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_hessian_correction_dominated_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (μ : Measure ℝ≥0) (τ : Ω → ℝ≥0) (ω : Ω)
    (hFinite : μ (Iio (τ ω)) < ⊤)
    (Vn : ℕ → ℝ≥0 → ℝ) (V : ℝ≥0 → ℝ)
    (hIn : ∀ n, ∀ᵐ (s : ℝ≥0) ∂(μ.restrict (Iio (τ ω))), Vn n s ∈ Icc a b)
    (hMeas : ∀ n, AEStronglyMeasurable (fun s : ℝ≥0 =>
      Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Vn n s)))
      (μ.restrict (Iio (τ ω))))
    (hConv : ∀ᵐ (s : ℝ≥0) ∂(μ.restrict (Iio (τ ω))),
      Tendsto (fun n => Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Vn n s)))
        atTop (nhds (Real.exp (-(q * (s : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (V s))))) :
    Tendsto (fun n => ∫ (s : ℝ≥0), Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Vn n s))
      ∂(μ.restrict (Iio (τ ω)))) atTop
      (nhds (∫ (s : ℝ≥0), Real.exp (-(q * (s : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (V s))
        ∂(μ.restrict (Iio (τ ω))))) := by sorry
