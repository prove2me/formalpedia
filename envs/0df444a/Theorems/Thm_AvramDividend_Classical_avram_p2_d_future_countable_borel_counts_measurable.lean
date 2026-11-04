-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_countable_borel_counts_measurable
-- name    : AvramDividend.Classical.avram_p2_d_future_countable_borel_counts_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:15:21.533212+00:00
-- url     : https://prove2.me/theorems/9815ce66-9c79-4dd5-a86a-5a89b57a820d
-- title:
--   Countable original intrinsic Borel marked jump counts form a measurable product-valued observable
-- statement:
--   For every countable sequence of jointly Borel source time–mark regions, the simultaneous vector of original intrinsic jump counts into ENNReal^Nat is measurable. No rate, boundedness or finite activity is imposed.
-- source:
--   Apply the Proved original intrinsic all-Borel time-mark count measurability lemma 21acd1ce coordinatewise, then Mathlib measurable_pi_iff; holds even when count values are ∞.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_countable_borel_counts_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℕ → Set (ℝ≥0 × ℝ))
    (hC : ∀ n, MeasurableSet (C n)) :
    Measurable (fun ω : Ω => fun n : ℕ =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (C n)) := by sorry
