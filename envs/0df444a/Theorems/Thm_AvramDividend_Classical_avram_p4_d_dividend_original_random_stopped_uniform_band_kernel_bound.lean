-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_uniform_band_kernel_bound
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_stopped_uniform_band_kernel_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:44:13.296221+00:00
-- url     : https://prove2.me/theorems/fbc21157-9da9-40c0-a828-00e1fc988a05
-- title:
--   Source-ordered dividend-gradient kernel uniformly bounded at original random ruin and stop clocks
-- statement:
--   For the original controlled Lévy reserve and each path's actual random extended ruin deadline and finite stopped time, a single fixed derivative bound K on a compact reserve band controls the signed discount-gradient kernel uniformly across all sample paths, whenever the source left-X/right-D reserve lies in the band νω-almost everywhere on true paymentTimes through its closed stopped horizon. The same K works for stochastic source/stop clocks and is independent of ω; the source right-payment and horizon convention is unchanged.
-- source:
--   Original X.X leftLim and rightLimit D prepayment reserve, original stopped paymentTimes, fixed band source bound 8e186779. Generalises already accepted deterministic uniform kernel 859b92b8 to sample-dependent true source clocks without an equality-in-law argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_stopped_uniform_band_kernel_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (ν : Ω → Measure ℝ)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (a b K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ y ∈ Icc a b, |deriv w y| ≤ K)
    (hstate : ∀ ω, ∀ᵐ s ∂(ν ω).restrict
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∀ ω, ∀ᵐ s ∂(ν ω).restrict (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
      ‖Real.exp (-(q * s)) *
        (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
          s.toNNReal - rightLimit D s.toNNReal ω))‖ ≤ 1 + K := by sorry
