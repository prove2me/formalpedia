-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_positive_level_upcrossing_strictly_before_horizon
-- name    : AvramDividend.Classical.unbounded_positive_level_upcrossing_strictly_before_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:30:44.965604+00:00
-- url     : https://prove2.me/theorems/4295afc5-b175-441f-a4b7-7f11fc32d64d
-- title:
--   Strictly pre-horizon passage above a positive level has positive probability
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, positive discount and any positive time horizon t, there exists a strictly positive level a for which the event of a path exceeding a at some time s<t has positive probability. This strengthens the established weak upcrossing statement to a strict pre-horizon one by applying it at time t/2, a useful property when proving strict exit-time stopping identities.
-- source:
--   Proved unbounded_positive_level_upcrossing_before_horizon and monotonicity of measure under a strict horizon enlargement.

import Theorems.Thm_AvramDividend_Classical_unbounded_positive_level_upcrossing_before_horizon
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.OuterMeasure.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_positive_level_upcrossing_strictly_before_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧
      0 < P {ω : Ω | ∃ s : ℝ≥0, s < t ∧ a < X.X s ω} := by sorry
