-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_payoff_zero_of_negative_initial_reserve
-- name    : AvramDividend.Classical.chat04_killed_scale_payoff_zero_of_negative_initial_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:29:04.249604+00:00
-- url     : https://prove2.me/theorems/c3f53629-7308-4599-b178-96bb8e2dd636
-- title:
--   Killed discounted scale payoff vanishes from negative starting capital
-- statement:
--   For any spectrally negative Levy process started from reserve x<0, the survival condition up to each time t is false because it includes s=0 and X(0)=0. Therefore the killed discounted scale payoff is identically zero, pointwise for every sample path, every t, and arbitrary q and W. This isolates the negative-initial-reserve case of the killed q-scale martingale.
-- source:
--   Direct from the initial value X_0=0 in SpectrallyNegativeLevy and the exact pathwise killed-survival indicator.

import Mathlib.Algebra.Notation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_scale_payoff_zero_of_negative_initial_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (hx : x < 0) (W : ℝ → ℝ) (t : ℝ≥0) (ω : Ω) :
    ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
      (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω = 0 := by sorry
