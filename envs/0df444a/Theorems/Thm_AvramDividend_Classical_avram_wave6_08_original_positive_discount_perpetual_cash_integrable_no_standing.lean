-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_integrable_no_standing
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_discount_perpetual_cash_integrable_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:53:16.894172+00:00
-- url     : https://prove2.me/theorems/2bc682fb-927b-4fb1-941b-6144bf320e4e
-- title:
--   Any genuine original Lévy full perpetual dividend cash L1 at all positive discount q, without Standing
-- statement:
--   For every original spectrally negative Lévy X, any admissible capped D and any positive discount q, the real full untruncated original pre-ruin Stieltjes payout is P-integrable. No Standing needed: source ψ continuous at 0 and ψ(0)=0 permit a small positive θ with ψθ<q.
-- source:
--   True source ψ continuity 1fa27b74 and ψ(0)=0 88416f41; full source θ-perpetual cash integrable 5b1a666c. Strengthens previous Standing-only 2d1232f2. Needed to eliminate artificial q≥ψ1/Standing restrictions for source stochastic stopped cash L1 in corrected UBV.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_stieltjes_cash_integrable_q_ge_psi
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_positive_discount_perpetual_cash_integrable_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by sorry
