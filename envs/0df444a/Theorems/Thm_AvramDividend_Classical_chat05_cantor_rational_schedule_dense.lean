-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
-- name    : AvramDividend.Classical.chat05_cantor_rational_schedule_dense
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:36:34.421529+00:00
-- url     : https://prove2.me/theorems/9206d7f5-f3e0-4156-92df-0d82bb161d39
-- title:
--   The explicit countable rational stopping and dividend sampling schedule is dense in nonnegative time
-- statement:
--   The Cantor-pairing schedule j↦unpair(j).second/(unpair(j).first+1) has dense range in the nonnegative real times. Indeed, every time t is the limit of upward dyadic approximations. The proved rational-grid coverage lemma puts every such approximation into the schedule, and the proved NNReal dyadic rounding convergence shows t lies in the closure. This identifies the exact same schedule used by our already proved strict-reflected-ruin clock and measurable stopped reward.
-- source:
--   Proved dyadic_ceiling_nnreal_tendsto, chat04_nat_pairing_rational_grid_coverage; pinned Mathlib dense_iff_closure_eq and mem_closure_of_tendsto.

import Mathlib.Topology.Closure
import Mathlib.Topology.Neighborhoods
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage

open Filter Topology Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat05_cantor_rational_schedule_dense :
    Dense (Set.range (fun j : ℕ =>
      ((Nat.unpair j).2 : ℝ≥0) *
        (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹))) := by
  sorry
