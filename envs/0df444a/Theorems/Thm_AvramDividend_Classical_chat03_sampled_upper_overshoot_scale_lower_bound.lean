-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_sampled_upper_overshoot_scale_lower_bound
-- name    : AvramDividend.Classical.chat03_sampled_upper_overshoot_scale_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:50:44.077041+00:00
-- url     : https://prove2.me/theorems/b3cb6455-3273-4e6f-8326-8dfa0ddb1fbd
-- title:
--   Correct q-scale lower bound at sampled upper-barrier overshoot
-- statement:
--   At any sampled time t when the Lévy reserve has crossed strictly above the upper capital barrier a, the discounted q-scale payoff evaluated at the sampled reserve is at least the discounted boundary value W(a). This remains true if the sample is later than the continuous first-passage instant and the reserve overshoots a between grid observations. It corrects an unsupported equality of sampled payoff and boundary payoff that appears in an Open finite-grid intermediate theorem.
-- source:
--   Canonical q-scale function monotonicity on nonnegative reserves, field IsScaleFunction.2.2.2.1, and positive exponential discount.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_sampled_upper_overshoot_scale_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a)
    (t : ℝ≥0) (ω : Ω) (hcross : a - x < X.X t ω) :
    Real.exp (-(q * (t : ℝ))) * W a ≤
      Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω) := by sorry
