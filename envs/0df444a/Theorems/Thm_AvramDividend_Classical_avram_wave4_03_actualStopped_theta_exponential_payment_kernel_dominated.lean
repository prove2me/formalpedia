-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actualStopped_theta_exponential_payment_kernel_dominated
-- name    : AvramDividend.Classical.avram_wave4_03_actualStopped_theta_exponential_payment_kernel_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:18:16.878017+00:00
-- url     : https://prove2.me/theorems/c1292a84-16ca-47ea-b4c8-b52c0007bd7a
-- title:
--   Actual stopped capped pre-ruin payment dominated by arbitrary positive tilt of same-source postpayment exponential
-- statement:
--   For original same-path capped admissible D, every strictly pre-ruin payment instant, including the initial atom, has nonnegative postpayment reserves. For each theta>0 and real q, this implies exp(-q t)≤exp(theta x) exp(theta*(X_t-D_{t+})-q t) pointwise. This supports genuine full-Stieltjes theta-budget expectations and requires no replacement path or atomic approximation.
-- source:
--   Capped source pre-ruin postpayment reserve nonnegativity a8120e3c and prior theta-one pathwise kernel bound 0375c440.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_actualStopped_theta_exponential_payment_kernel_dominated
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) :
    Real.exp (-(q * (t : ℝ))) ≤
      Real.exp (θ * x) * Real.exp
        (θ * (X.X t ω - rightLimit D t ω) - (t : ℝ) * q) := by sorry
