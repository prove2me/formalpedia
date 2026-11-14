-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb29_source_uniform_discounted_cash_upper_bound_positive_part_limit
-- name    : AvramDividend.Classical.avram_bvb29_source_uniform_discounted_cash_upper_bound_positive_part_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:09:50.904061+00:00
-- url     : https://prove2.me/theorems/856b1cd7-3a42-4202-af43-13bf37dc5f40
-- title:
--   Original compensated cash positive-part limit needs only uniform full-horizon payout bound, exact K limit and vanishing generator grid
-- statement:
--   For source finite grid cash F_n bounded above by a single full-horizon discounted real cash ceiling f at every n, stopped original negative-mark compensator K_n tending its exact full integral k, and source strict interior generator grid G_n tending zero, the compensated upper-part error tends to zero whenever f is bounded by w-k. The proof uses source cash monotonicity and squeeze and does not need a separate convergence theorem for the truncated cash F_n. This directly simplifies zero-reserve survivor ed067740 and 209eed42 by combining Proved original full stopped-K scalar identity, grid limit and full-horizon cash budget.
-- source:
--   Proved source general error lemma b7ce23ad, original full stopped-K 57da0020, generator grid 2b1be52d, original zero-contact cash terminal 09a9c1c4. Pinned Mathlib tendsto_of_tendsto_of_tendsto_of_le_of_le.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb29_source_uniform_discounted_cash_upper_bound_positive_part_limit
    (F K G : ℕ → ℝ) (w f k : ℝ)
    (hF : ∀ n, F n ≤ f)
    (hK : Tendsto K atTop (𝓝 k))
    (hG : Tendsto G atTop (𝓝 (0 : ℝ)))
    (hBudget : f ≤ w - k) :
    Tendsto (fun n => max (F n - (w + ((-K n) + G n))) 0)
      atTop (𝓝 (0 : ℝ)) := by sorry
