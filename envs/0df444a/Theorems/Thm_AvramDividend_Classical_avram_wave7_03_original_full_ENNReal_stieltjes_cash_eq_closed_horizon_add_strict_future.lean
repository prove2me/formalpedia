-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ENNReal_stieltjes_cash_eq_closed_horizon_add_strict_future
-- name    : AvramDividend.Classical.avram_wave7_03_original_full_ENNReal_stieltjes_cash_eq_closed_horizon_add_strict_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T22:01:05.536725+00:00
-- url     : https://prove2.me/theorems/e965e831-32e9-440c-a377-3f282ca90c06
-- title:
--   Complete source ENNReal Stieltjes payment equals closed-horizon cash plus strict-future cash, atom-exact
-- statement:
--   For the actual original Lévy process, ruin clock, and genuine cumulative-dividend Stieltjes measure, the complete full discounted ENNReal payout on paymentTimes(ruinTime) is the sum of its restriction to paymentTimes∩Iic T and the strictly future remainder paymentTimes∩Ioi T. Holds even if the payout is infinite, for any real q and T. Every time-zero or horizon right-limit payment atom and continuous mass occurs exactly once, with the horizon atom included on the closed side and positive ruin-boundary mass excluded by paymentTimes.
-- source:
--   Proved source paymentTimes_measurable and exact pinned Mathlib MeasureTheory.lintegral_union signature, Set partition, no process replacement.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_full_ENNReal_stieltjes_cash_eq_closed_horizon_add_strict_future
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q T : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
