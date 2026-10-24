-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_initial_reserve_killed_scale_martingale
-- name    : AvramDividend.Classical.negative_initial_reserve_killed_scale_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:43:18.034668+00:00
-- url     : https://prove2.me/theorems/d1ba611c-a95b-49d2-be4d-ae4e41e4c009
-- title:
--   The downward-killed q-scale payoff is identically zero and a martingale for strictly negative starting capital
-- statement:
--   For any spectrally negative Lévy process whose path starts at X_0=0, strictly negative initial capital x<0, any real q and any scale-like payoff W, the downwards killed process 1_{∀s≤t, 0≤x+X_s} exp(-q t) W(x+X_t) vanishes identically at every t≥0. The survival event includes s=0, where x+X_0=x<0; hence its indicator is zero, without probabilistic regularity assumptions. The zero process is a martingale by pinned Mathlib martingale_zero. This discharges the negative-initial-capital branch of chat04_unbounded_killed_discounted_scale_martingale and makes clear why the survival condition is necessary.

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.negative_initial_reserve_killed_scale_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : x < 0) (q : ℝ) (W : ℝ → ℝ) :
    Martingale
      (fun t ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}.indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω))
      𝓕 P := by sorry
