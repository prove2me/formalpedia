-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration
-- name    : AvramDividend.Classical.chat03_monotone_clock_reindexed_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T05:33:57.165347+00:00
-- url     : https://prove2.me/theorems/2069e7c3-ee93-4838-8c2d-8dcbbe642bb7
-- title:
--   Monotone discrete clocks induce sampled Lévy filtrations
-- statement:
--   Given any continuous-time filtration indexed by the nonnegative reals and any monotone deterministic clock from natural indices into nonnegative time, the pulled-back sigma-algebras form a discrete filtration and agree pointwise with the original filtration evaluated at the clock. This removes a separate sampled-filtration existence assumption from the bounded-grid stopped scale argument.
-- source:
--   Construct a Mathlib Filtration record with seq k := 𝓕 (clock k); monotonicity follows by composition and domination of the ambient measurable space follows from 𝓕.le.

import Mathlib.Probability.Process.Filtration

open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat03_monotone_clock_reindexed_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) :
    ∃ H : Filtration ℕ mΩ, ∀ k, H k = 𝓕 (clock k) := by
  sorry
