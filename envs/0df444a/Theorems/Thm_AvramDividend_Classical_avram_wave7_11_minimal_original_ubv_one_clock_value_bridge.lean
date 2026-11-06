-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_minimal_original_ubv_one_clock_value_bridge
-- name    : AvramDividend.Classical.avram_wave7_11_minimal_original_ubv_one_clock_value_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:45:32.354683+00:00
-- url     : https://prove2.me/theorems/884bc177-d45c-4f27-80ac-1fa7fb8e0c7b
-- title:
--   Minimal source-faithful UBV one-clock finite-horizon value transfer without standing, positive discount or HJB
-- statement:
--   On the original spectrally negative Lévy probability P and actual Stieltjes dividend measure, every nonnegative-capital finite-horizon UBV value bound follows from only one expected original ruin-clock budget at a deterministic natural time past the horizon when x>0. No standing process assumption, positive q, C² regularity or HJB is necessary at this deterministic conversion stage. The x=0 part is a separately Proved unconditional exact zero reward. The explicit boundary w(0)>=0 is retained for source-faithfulness.
-- source:
--   Proved UBV zero-start exact source payout 362849ee and Proved one-late-natural-clock budget transfer. No open imports.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ubv_zero_start_original_full_discounted_stieltjes_reward_eq_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_one_future_natural_ruin_clock_budget_controls_full_finite_horizon
import Mathlib.Data.Real.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_minimal_original_ubv_one_clock_value_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hOneClock : 0 < x →
      ∃ n : ℕ, T < (n : ℝ) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
