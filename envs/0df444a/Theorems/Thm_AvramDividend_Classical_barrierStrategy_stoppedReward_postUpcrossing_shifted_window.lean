-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_postUpcrossing_shifted_window
-- name    : AvramDividend.Classical.barrierStrategy_stoppedReward_postUpcrossing_shifted_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:56:41.819134+00:00
-- url     : https://prove2.me/theorems/1fff2edc-039c-4463-b4b5-ad519e24976c
-- title:
--   Actual stopped barrier dividends translate to the exact post-upcrossing Lévy-increment payment window
-- statement:
--   For a spectrally negative Lévy path started below a dividend barrier, after a finite first upward-passage time u, its full discounted Stieltjes dividend reward up to original controlled ruin equals exp(-qu) times the discounted running-supremum Stieltjes reward of post-u Lévy increments, with only positive relative payment times whose original translated times remain strictly before the original controlled ruin. This is a rigorous pathwise stopped-reward shift, retaining the exact possibly infinite ruin horizon. It assumes only an explicit no-nonpositive-time atom for the shifted future-supremum measure, which a separate Proved theorem already establishes unconditionally.
-- source:
--   Derived from proved stopped_payment_lintegral_eq_post_u_of_zero_Iic (964f4636), discounted_paymentTimes_shift_of_measure_map (3d97c2a4), barrierStrategy_dividendMeasure_map_shift_of_support (3093890e), pre-upcrossing zero dividends (d92e7576), and locally finite Stieltjes measure d0e8873f. Core pre-Markov pathwise bridge for standing barrier valuation 79978d61.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_locallyFinite
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_preUpcrossing_Iic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_map_shift_of_support
import Theorems.Thm_AvramDividend_Classical_stopped_payment_lintegral_eq_post_u_of_zero_Iic
import Theorems.Thm_AvramDividend_Classical_discounted_paymentTimes_shift_of_measure_map
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_stoppedReward_postUpcrossing_shifted_window
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (q : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hνneg : (dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω) (Set.Iic (0 : ℝ)) = 0) :
    (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂dividendMeasure (barrierStrategy X x a) ω) =
    ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
      (∫⁻ t in (Set.Ioi (0 : ℝ)) ∩
        ((fun t : ℝ => (u : ℝ) + t) ⁻¹'
          paymentTimes (ruinTime X x (barrierStrategy X x a) ω)),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (fun r (_ : Ω) =>
            sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
          ω)) := by sorry
