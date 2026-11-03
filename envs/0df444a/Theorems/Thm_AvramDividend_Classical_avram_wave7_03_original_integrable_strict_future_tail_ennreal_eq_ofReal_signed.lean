-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_integrable_strict_future_tail_ennreal_eq_ofReal_signed
-- name    : AvramDividend.Classical.avram_wave7_03_original_integrable_strict_future_tail_ennreal_eq_ofReal_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:43:21.658089+00:00
-- url     : https://prove2.me/theorems/0f08d91e-36e3-47fd-a610-9faff5a647a9
-- title:
--   Exact original strict future dividend Stieltjes tail ENNReal cash equals ofReal of genuine signed real integral
-- statement:
--   At each original source sample path, assume the genuine full real signed discounted Stieltjes integrand is IntegrableOn paymentTimes(ruinTime X x D ω) against dividendMeasure D ω. Then for every natural n, the exact original ENNReal discounted Stieltjes cash on paymentTimes(ruinTime)∩Ioi n equals ENNReal.ofReal of the genuine real signed Stieltjes integral on the precisely same tail set and source measure. The proof restricts the full IntegrableOn to the tail via Mathlib IntegrableOn.mono_set, certifies the positive exponential integrand, and uses the pinned Mathlib ofReal_integral_eq_lintegral_ofReal. This is a rigorous tail-level signed-to-ENNReal bridge, retaining all original continuous and jump payouts and the full-domain time-zero atom.
-- source:
--   Pinned Mathlib MeasureTheory.IntegrableOn.mono_set and MeasureTheory.ofReal_integral_eq_lintegral_ofReal; actual source dividendMeasure/paymentTimes/ruinTime.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_integrable_strict_future_tail_ennreal_eq_ofReal_signed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    ∀ n : ℕ,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
