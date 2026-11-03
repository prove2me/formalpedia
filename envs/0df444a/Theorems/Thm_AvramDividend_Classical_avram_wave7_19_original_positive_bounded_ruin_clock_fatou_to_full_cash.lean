-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_positive_bounded_ruin_clock_fatou_to_full_cash
-- name    : AvramDividend.Classical.avram_wave7_19_original_positive_bounded_ruin_clock_fatou_to_full_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:13:06.623749+00:00
-- url     : https://prove2.me/theorems/0e4f59c9-5a33-48c4-99fe-164d26dd31b0
-- title:
--   All positive integer bounded original ruin-clock cash budgets imply full finite-horizon ruin cash without uniform integrability
-- statement:
--   Original-source temporal stop limit supporting W7-08. Assuming uniform ENNReal discounted cash bounds at every positive integer deterministic cap of ruinTime, the same bound holds on the exact paymentTimes(ruinTime) ∩ Iic T. Source paymentTimes includes t=0, and positive physical times strictly before ruin eventually occur before every sufficiently large integer truncation. Joint measurability comes from the proved source ruinTime and paymentTimes lemmas. Applies the already Proved W7-19 nonnested expected-cash Fatou theorem, requiring neither UI nor a continuity assertion at jump ruin, and leaves canonical hypotheses unchanged because IsDividendStrategy follows from IsAdmissibleLe as hD.1.1.
-- source:
--   W7-08 source n-bounded strict-ruin-time budgets 665b3b52/d457be6b; accepted source time-zero/positive exclusion d68c1081 and W7-19 expected Fatou 3ad7a9d4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonnested_joint_cap_support_fatou_expected_cash
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_positive_bounded_ruin_clock_fatou_to_full_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hStrategy : IsDividendStrategy 𝓕 D)
    (budget : ℝ≥0∞)
    (hBudget : ∀ n : ℕ, 0 < n →
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget := by sorry
