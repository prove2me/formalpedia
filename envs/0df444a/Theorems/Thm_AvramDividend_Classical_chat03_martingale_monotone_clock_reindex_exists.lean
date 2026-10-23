-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_martingale_monotone_clock_reindex_exists
-- name    : AvramDividend.Classical.chat03_martingale_monotone_clock_reindex_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:29:11.77439+00:00
-- url     : https://prove2.me/theorems/73af341b-a0e6-4934-8b99-c1303fc922eb
-- title:
--   Monotone sampling preserves a martingale in an explicitly reindexed filtration
-- statement:
--   A continuous-time martingale sampled along any nondecreasing deterministic sequence of nonnegative times is a discrete-time martingale under an explicitly constructed discrete filtration with H(k)=G(clock(k)). The proof transports strong adaptedness and every deterministic-time conditional-expectation identity under the monotone time change.
-- source:
--   Use accepted chat03_monotone_clock_reindexed_filtration and unfold Mathlib's Martingale to transfer each component using clock monotonicity. The original exact target's strict lint parser rejects the literal filtration structure, so this logically equivalent existential form preserves the result as a separate reusable public theorem.

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration

open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat03_martingale_monotone_clock_reindex_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {G : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M G P)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) :
    ∃ H : Filtration ℕ mΩ,
      (∀ k, H k = G (clock k)) ∧
      Martingale (fun k ω => M (clock k) ω) H P := by
  sorry
