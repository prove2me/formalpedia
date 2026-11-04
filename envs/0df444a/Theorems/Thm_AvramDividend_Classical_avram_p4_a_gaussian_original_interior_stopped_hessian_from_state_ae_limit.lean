-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_interior_stopped_hessian_from_state_ae_limit
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_hessian_from_state_ae_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:19:31.329882+00:00
-- url     : https://prove2.me/theorems/ddea466e-9960-4a9a-ab81-f10533749257
-- title:
--   Original Levy Gaussian stopped Hessian correction convergence from a.e. interior state convergence
-- statement:
--   For the actual source Gaussian variance coefficient and function w C2 only on the strict positive interior, if stopped reserve approximants and their a.e. limit lie in one compact interior band, and the states converge almost everywhere, the corresponding discounted sigma squared over two Hessian corrections converge through the finite stopped time integral. Genuine state convergence and measurability remain localising premises for P4-E.
-- source:
--   Proved source-specific interior Hessian state continuity and stopped dominated convergence, Avram Palmowski Pistorius Proposition 4(i) equation (5.10).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_discounted_interior_hessian_state_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_interior_stopped_hessian_correction_dominated_limit
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_hessian_from_state_ae_limit
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
    (hIn : ∀ n, ∀ᵐ (s : ℝ≥0) ∂(μ.restrict (Iio (τ ω))),
      Vn n s ∈ Icc a b)
    (hVin : ∀ᵐ (s : ℝ≥0) ∂(μ.restrict (Iio (τ ω))),
      V s ∈ Icc a b)
    (hMeas : ∀ n, AEStronglyMeasurable (fun s : ℝ≥0 =>
      Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Vn n s)))
      (μ.restrict (Iio (τ ω))))
    (hVconv : ∀ᵐ (s : ℝ≥0) ∂(μ.restrict (Iio (τ ω))),
      Tendsto (fun n => Vn n s) atTop (nhds (V s))) :
    Tendsto (fun n => ∫ (s : ℝ≥0),
        Real.exp (-(q * (s : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Vn n s))
      ∂(μ.restrict (Iio (τ ω)))) atTop
      (nhds (∫ (s : ℝ≥0), Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (V s))
        ∂(μ.restrict (Iio (τ ω))))) := by sorry
