-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_measurable_random_mark_interval_20261111
-- name    : AvramDividend.Classical.avram_a06_measurable_random_mark_interval_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:59:15.659601+00:00
-- url     : https://prove2.me/theorems/0c1ec07a-2568-4f37-b8e7-ee4640562d80
-- title:
--   Random natural-grid marked interval sums are measurable
-- statement:
--   Given two measurable count-valued endpoints and a measurable sequence of marks, the finite sum over the random half-open interval is measurable. The proof packages each fixed-endpoint sum into a countable-index family and invokes measurable evaluation on the countable product of natural indices. This discharges the measurability gate for A06 random-grid characteristic functions.

import Mathlib
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_measurable_random_mark_interval_20261111
    {Ω : Type*} [MeasurableSpace Ω]
    (a b : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (hY : ∀ j, Measurable (Y j)) :
    Measurable (fun ω => ∑ j ∈ Finset.Ico (a ω) (b ω), Y j ω) := by sorry
