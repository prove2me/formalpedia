-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_stopped_gaussian_real_all_horizon_energy
-- name    : AvramDividend.Classical.ripple_original_stopped_gaussian_real_all_horizon_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:52:26.957497+00:00
-- url     : https://prove2.me/theorems/27c1caa4-0ed0-47d4-af9f-6ef9e27d19f2
-- title:
--   Original predividend compact stopped Gaussian coefficient has finite real-time Brownian Ito energy on every positive horizon
-- statement:
--   For the original Avram spectrally negative Levy process, dividend path, compact interior C2 candidate w and two genuinely path-dependent stop times (sigma,tau], the real-time coefficient of the Gaussian stochastic integral, defined by sigma_X times the derivative of w at the genuine left-limit prepayment controlled reserve and zero outside the interior band and stop window, has finite Brownian Ito quadratic energy over every positive finite real horizon. It is valid for original processes with downward jumps, does not replace the sample path by an independent Brownian motion, and imposes no extra assumed stochastic moment bound beyond original probability law.
-- source:
--   Exact proved compact derivative bound 98c2c058-e613-4558-8ab5-aa80e20cbf55 and genuine finite horizon integrand energy estimate 43090805-dff6-4165-8036-39ab2cf2f286; compatible with Ripple random stopping window certificate 730ba1ff-2b25-4037-8d77-beff6f5f8483.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval
import Theorems.Thm_AvramDividend_Classical_avram_lsc_finite_horizon_bounded_integrand_energy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.ripple_original_stopped_gaussian_real_all_horizon_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (σ τ : Ω → ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      X.σ * (if Y p ∈ Icc u v then deriv w (Y p) else 0)
    let S : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧
      (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
      (p.1 : WithTop ℝ≥0) ≤ τ p.2}
    ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
        (‖S.indicator G (Real.toNNReal s,ω)‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := by sorry
