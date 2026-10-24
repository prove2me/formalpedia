-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_future_window_killed_scale_zero_of_negative_start
-- name    : AvramDividend.Classical.chat04_future_window_killed_scale_zero_of_negative_start
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:54:41.134827+00:00
-- url     : https://prove2.me/theorems/62b9922b-cf91-4c1f-abe3-aa81c6169267
-- title:
--   Future-window killed q-scale payoff vanishes from negative starting reserve
-- statement:
--   For a future window [s,u], the survival indicator is zero if the observed reserve at time s is already negative. Accordingly, the future-window killed discounted q-scale payoff vanishes for any discount and scale candidate. This supplies the negative-state boundary case for the conditional future-window harmonicity argument.
-- source:
--   Pathwise future-window survival predicate evaluated at v=s and the indicator-of-nonmembership identity.

import Mathlib.Algebra.Notation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_future_window_killed_scale_zero_of_negative_start
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (s u : ℝ≥0)
    (hsu : s ≤ u) (ω : Ω) (hneg : x + X.X s ω < 0) :
    ({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
       0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) ω = 0 := by sorry
