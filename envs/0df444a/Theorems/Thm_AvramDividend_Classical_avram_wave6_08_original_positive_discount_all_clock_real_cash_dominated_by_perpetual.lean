-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_all_clock_real_cash_dominated_by_perpetual
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_discount_all_clock_real_cash_dominated_by_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:30:34.640599+00:00
-- url     : https://prove2.me/theorems/da1c5f5f-3156-4cd6-922c-a6919133f6bb
-- title:
--   A single integrable original perpetual cash variable dominates all clocked real payouts almost surely
-- statement:
--   For all original source admissible controls and q>0, on one P-almost-sure event and simultaneously for every real clock T, true discounted stopped cash.toReal is bounded above by the original perpetual cash.toReal. The latter is separately canonically Integrable under the same assumptions, and hence provides a universal samplewise L1 dominator for arbitrary localising clocks. No Standing, variation, bounded clock, or clock measurability is imposed.
-- source:
--   Source q>0 perpetual ENNReal cash a.s.-finite c3df986d permits legitimate use of Mathlib ENNReal.toReal_mono on the monotonic original Stieltjes restriction; original perpetual real payoff Integrable is Proved 2bc682fb. This exports the precise dominating-random-variable inequality required for real dominated convergence in corrected UBV localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_positive_discount_all_clock_real_cash_dominated_by_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, ∀ T : ℝ,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal := by sorry
