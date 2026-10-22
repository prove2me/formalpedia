-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_sampled_upper_event_payoff_le_killed_scale
-- name    : AvramDividend.Classical.chat03_sampled_upper_event_payoff_le_killed_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:56:00.178254+00:00
-- url     : https://prove2.me/theorems/d9fa5414-0f82-4d8f-b194-0770253db958
-- title:
--   Sampled upper-exit discounted boundary reward is bounded by sampled lower-killed scale reward
-- statement:
--   For any spectrally negative Lévy sample value, positive capital barrier a, and q-scale W, the discounted W(a) reward for an observed strict upward exit is at most the discounted sampled reserve scale value killed when the observed state is below -x. This handles three cases: observed lower exit, observed upper exit with possible sampled overshoot, and observed interior reserve. It is a pointwise inequality, valid without stochastic martingality or exact upper-boundary attainment between grid observations.
-- source:
--   Direct IsScaleFunction nonnegativity and monotonicity, with strict barrier separation from a>0.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_sampled_upper_event_payoff_le_killed_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a)
    (t : ℝ≥0) (ω : Ω) :
    (if a - x < X.X t ω then
        Real.exp (-(q * (t : ℝ))) * W a else 0) ≤
      (if X.X t ω < -x then 0 else
        Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) := by sorry
