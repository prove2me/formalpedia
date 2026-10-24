-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_payoff_zero_after_observed_ruin
-- name    : AvramDividend.Classical.chat04_killed_scale_payoff_zero_after_observed_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:49:12.081125+00:00
-- url     : https://prove2.me/theorems/6155e71c-e03a-4a01-b4a3-af25d92fda31
-- title:
--   Killed discounted q-scale payoff vanishes after any observed negative reserve
-- statement:
--   Whenever the reserve x + X_s is negative at an observed time s, the path has already failed the nonnegative survival condition. Consequently, for every later t ≥ s, the killed discounted scale payoff at t is exactly zero, regardless of the scale candidate and discount rate.
-- source:
--   Pathwise indicator identity and the definition of lower-survival killing.

import Mathlib.Algebra.Notation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_scale_payoff_zero_after_observed_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (s t : ℝ≥0)
    (hst : s ≤ t) (ω : Ω) (hneg : x + X.X s ω < 0) :
    ({u : Ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v u}).indicator
      (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω = 0 := by sorry
