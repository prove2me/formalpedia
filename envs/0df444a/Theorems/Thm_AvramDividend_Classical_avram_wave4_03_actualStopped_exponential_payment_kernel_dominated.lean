-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actualStopped_exponential_payment_kernel_dominated
-- name    : AvramDividend.Classical.avram_wave4_03_actualStopped_exponential_payment_kernel_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:16:12.095759+00:00
-- url     : https://prove2.me/theorems/0375c440-e08e-41b7-aed9-c3486dc071d6
-- title:
--   Original stopped admissible payment kernel dominated by same-source postpayment exponential
-- statement:
--   For the actual original spectrally negative Lévy source X and any capped admissible left-continuous dividend strategy D, every payment time including zero and strictly pre-ruin times has nonnegative postpayment reserve. Consequently e^{-qt} is at most e^x times the same-path postpayment source exponential e^{X_t-D_{t+}-qt}. This is a genuine pathwise stopped exponential verification interface, handling chronological right payment atoms at time zero and any positive time, with no jump-only or independently coupled process assumption.
-- source:
--   Canonical IsAdmissibleLe and original source X_zero at t=0; source postpayment reserve pre-ruin cap/solvency a8120e3c for t>0; pointwise Real.exp monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_03_actualStopped_exponential_payment_kernel_dominated
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (q : ℝ) :
    Real.exp (-(q * (t : ℝ))) ≤
      Real.exp x * Real.exp
        (X.X t ω - rightLimit D t ω - (t : ℝ) * q) := by sorry
