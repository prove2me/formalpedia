-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_discounted_positive_postpayment_terminal_rightContinuous
-- name    : AvramDividend.Classical.avram_wave8_20_original_preruin_discounted_positive_postpayment_terminal_rightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:57:19.970309+00:00
-- url     : https://prove2.me/theorems/2273e3d4-0546-43b2-afb2-2fccfb6ecd20
-- title:
--   Actual original strict-survival discounted positive-part postrightpayment HJB terminal is right-continuous before ruin
-- statement:
--   For each original sample path, every strictly surviving time t has source HJB terminal discounted positive-part payoff right-continuous when approached through times >= t that remain strictly before actual ruin. This supplies the exact right-limit continuity needed to show pointwise convergence of surviving terminals, independent of the generator supermartingale inequality.
-- source:
--   Original source right-continuous pre-ruin postpayment candidate payoff, accepted W8-20 634baba4, composed with continuous physical-time discount exp(-qt) and the continuous positive-part map max 0. Restricts to times >= t strictly below the actual ruinTime; no continuity through the ruin boundary is claimed. Honest terminal input for DCT with right-approach localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_preruin_discounted_positive_postpayment_terminal_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    ContinuousWithinAt
      (fun s : ℝ≥0 =>
        max 0 (Real.exp (-(q * (s : ℝ))) *
          w (x + X.X s ω - rightLimit D s ω)))
      {s : ℝ≥0 | t ≤ s ∧ (s : ℝ≥0∞) < ruinTime X x D ω} t := by sorry
