-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_natural_clock_cofinal_stieltjes_cash_eventually_exact
-- name    : AvramDividend.Classical.avram_sweep16_original_natural_clock_cofinal_stieltjes_cash_eventually_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:58:49.620917+00:00
-- url     : https://prove2.me/theorems/fd7f8c61-c825-44eb-8fe5-b5ff71412494
-- title:
--   Physical original natural finite ruin-clock Stieltjes cash stabilizes exactly under exhausting right-continuous stopping localizers
-- statement:
--   For the same actual spectrally negative Levy process X, original admissible dividend D, natural finite ruin clock min(ruinTime,n), and any increasing sequence of right-continuous-filtration stopping localizers S_k exhausting infinity pointwise, the localised exact closed original dividend-measure cash integral is eventually literally equal to the natural-clock integral on each original sample path. This preserves time-zero and eligible right-payment atoms at the stopping boundary; no replacing X, P, D, dividendMeasure or paymentTimes, and no martingale UI assumption.
-- source:
--   Same physical SWEEP16 750ad13b natural ruin clock and closed cash, using pinned lt_iSup_iff and min_le_right monotonicity; independent localisation limit prerequisite for public Fatou helper da912121.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_natural_clock_cofinal_stieltjes_cash_eventually_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k))
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ ω, (⨆ k : ℕ, S k ω) = ⊤) :
    ∀ ω, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
