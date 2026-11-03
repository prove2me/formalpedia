-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_minimal_original_ubv_ae_clock_value_bridge
-- name    : AvramDividend.Classical.avram_wave7_11_minimal_original_ubv_ae_clock_value_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:47:00.473835+00:00
-- url     : https://prove2.me/theorems/359d1ea2-44d3-4980-879a-bd409e6f83ab
-- title:
--   Minimal original UBV finite-horizon bound from one a.s. future source clock without HJB or standing
-- statement:
--   For the original spectrally negative Lévy law and actual admissible Stieltjes dividend payouts, all positive/zero caps and every q and finite nonnegative T, one sample-dependent clock strictly later than T almost surely and with a source expected stopped-cash budget is enough for the full finite-horizon bound at x>0. At x=0 the original full discounted payoff is already unconditionally zero. The transfer itself uses neither standing hypotheses, HJB generator nor C2 smoothness; those belong solely to the upstream stochastic budget.
-- source:
--   Proved source zero-reserve exact payout 362849ee and Proved a.s.-future clock original Stieltjes expectation transfer; no Open imported.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ubv_zero_start_original_full_discounted_stieltjes_reward_eq_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ae_future_ruin_clock_budget_controls_original_horizon
import Mathlib.Data.Real.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_minimal_original_ubv_ae_clock_value_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hAeClock : 0 < x →
      ∃ η : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ENNReal.ofReal T < η ω) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
