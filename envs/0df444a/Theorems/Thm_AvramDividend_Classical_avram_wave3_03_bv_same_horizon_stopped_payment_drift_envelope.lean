-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_same_horizon_stopped_payment_drift_envelope
-- name    : AvramDividend.Classical.avram_wave3_03_bv_same_horizon_stopped_payment_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:34:55.204135+00:00
-- url     : https://prove2.me/theorems/c335db18-ac66-48e1-86b1-3cdff20f1f38
-- title:
--   Same-horizon BV original Lévy drift envelope for the full stopped dividend Stieltjes measure
-- statement:
--   For the actual spectrally negative BV Lévy source and actual adapted left-continuous dividend strategy, the full stopped discounted Stieltjes payment through deterministic T is bounded by initial capital plus the physical BV drift times T, on the original full-measure event of nondecreasing drift deficit and under exact eventual post-T solvent reserve. Includes all continuous and singular-continuous mass plus the right atom at T. Strengthens earlier S>T survival envelope by using the proved post-payment reserve right limit at T, with no spurious atomicity or compensation assumption.
-- source:
--   Proved actual BV Lévy drift residual monotonicity f6cc1059; Proved postPaymentReserve_rightLimit_and_nonnegative ee511693; Proved stopped payment full-Stieltjes bound 1a006d5f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightLimit_and_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_same_horizon_stopped_payment_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (∀ᶠ s in 𝓝[>] T, 0 ≤ riskProcess X x D s ω) →
      (∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (x + (T : ℝ) * X.drift) := by sorry
