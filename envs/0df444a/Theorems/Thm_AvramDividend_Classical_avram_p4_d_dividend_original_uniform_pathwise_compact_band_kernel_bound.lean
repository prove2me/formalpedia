-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_uniform_pathwise_compact_band_kernel_bound
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_uniform_pathwise_compact_band_kernel_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:36:28.947363+00:00
-- url     : https://prove2.me/theorems/859b92b8-8b41-47e9-a447-88ea99d39e0b
-- title:
--   Deterministic uniform compact-band dividend-gradient kernel bound for every original path
-- statement:
--   For one fixed original Lévy reserve X and dividend control D, if one deterministic K bounds the derivative of w on a strict-interior compact reserve band and every path-dependent Stieltjes submeasure νω sees source prepayment reserve in that band almost everywhere on the true ruin-stopped closed paid clock, then the original discounted dividend-gradient correction kernel is uniformly bounded in absolute value by 1+K for all sample paths and νω-almost every paid time. The same deterministic K applies across sample paths, enabling eventual expectation-level integrability rather than sample-dependent norms.
-- source:
--   Original exact X.X leftLimit and dividend rightLimit reserve, original paymentTimes_membership_to_nNReal_active and measurable, genuine fixed compact-band derivative bound 8e186779. Original ff7facab proof factorisation, now quantified uniformly in ω.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_uniform_pathwise_compact_band_kernel_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ν : Ω → Measure ℝ)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (a b K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ y ∈ Icc a b, |deriv w y| ≤ K)
    (hstate : ∀ ω, ∀ᵐ s ∂(ν ω).restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∀ ω, ∀ᵐ s ∂(ν ω).restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      ‖Real.exp (-(q * s)) *
        (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
          s.toNNReal - rightLimit D s.toNNReal ω))‖ ≤ 1 + K := by sorry
