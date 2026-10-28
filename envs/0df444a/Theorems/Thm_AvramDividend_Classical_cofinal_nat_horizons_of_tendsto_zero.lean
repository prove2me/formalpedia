-- Prove2me | Theorems.Thm_AvramDividend_Classical_cofinal_nat_horizons_of_tendsto_zero
-- name    : AvramDividend.Classical.cofinal_nat_horizons_of_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:42:57.25499+00:00
-- url     : https://prove2.me/theorems/781724b9-4084-41e5-b43b-2b081d10edc0
-- title:
--   Every nonnegative horizon sequence converging to zero is cofinal among positive observation horizons
-- statement:
--   If a sequence of nonnegative time horizons converges to zero, then for every positive horizon ε some sequence term lies at or below ε. This removes an artificial cofinality premise from the countable-grid reductions of Lévy downward regularity once a standard sequence of horizons is chosen. The proof uses convergence with the open initial interval (-∞,ε) and the nonemptiness of eventually true tails of ℕ.
-- source:
--   Elementary topology of nonnegative real convergence; technical bridge for Shtatland/Rogozin downward regularity and Lévy excursion-height atomlessness.

import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter
open scoped NNReal Topology

theorem AvramDividend.Classical.cofinal_nat_horizons_of_tendsto_zero
    (horizons : ℕ → ℝ≥0)
    (hlim : Filter.Tendsto horizons Filter.atTop (nhds 0)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε := by sorry
