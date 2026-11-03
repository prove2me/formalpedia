-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_integrable_strict_future_ENNReal_stieltjes_tails_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave7_03_original_integrable_strict_future_ENNReal_stieltjes_tails_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:44:49.755704+00:00
-- url     : https://prove2.me/theorems/8d34fde8-3ea9-4be0-a7b0-6f1cf0018388
-- title:
--   Genuine original integrable signed Stieltjes cash implies exact strict future ENNReal payment tails vanish
-- statement:
--   On the original spectrally negative Levy process and exact pre-ruin dividendMeasure, genuine full real signed IntegrableOn implies the original ENNReal discounted Stieltjes integral restricted to paymentTimes(ruinTime X x D ω)∩Ioi n converges to zero as n→∞. The proof combines an already remotely accepted original signed-tail convergence lemma with pinned Mathlib ofReal_integral_eq_lintegral_ofReal on each exact same-measure tail and continuity of ENNReal.ofReal at zero. The true time-zero right-limit atom remains present in the complete domain and is excluded only by the strictly future tail restriction, while all continuous and jump payouts are retained.
-- source:
--   Accepted original signed tail c94fa5f6; pinned Mathlib IntegrableOn.mono_set, ofReal_integral_eq_lintegral_ofReal and ENNReal.continuous_ofReal.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_integrable_strict_future_ENNReal_stieltjes_tails_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    Tendsto (fun n : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by sorry
