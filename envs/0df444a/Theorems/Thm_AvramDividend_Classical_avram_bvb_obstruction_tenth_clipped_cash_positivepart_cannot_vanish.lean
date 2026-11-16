-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_clipped_cash_positivepart_cannot_vanish
-- name    : AvramDividend.Classical.avram_bvb_obstruction_tenth_clipped_cash_positivepart_cannot_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:50:15.450544+00:00
-- url     : https://prove2.me/theorems/034f8177-b918-4b9d-b326-fba846933090
-- title:
--   Uniform discounted tenth-horizon nojump cash gap refutes vanishing original physical drift-only positive error
-- statement:
--   For any sequences of original physical stopped cash F_n and strict-internal drift ledger L_n, if every n≥4 cash reward dominates (2/25+1/2)exp(−1/10) and all drift ledgers vanish, then max(F_n−(1/2+L_n),0) cannot converge to zero. This is the exact deterministic endpoint of the positive-cap original zero-barrier BV pathwise counterexample.
-- source:
--   Use Proved strict positive tenth-horizon cash gap f5055368 and Proved uniform eventual positive-part obstruction 1453dade with ε=(2/25+1/2)exp(−1/10)−1/2>0.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_eventual_uniform_positive_cash_gap_refutes_zero_limit
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_clipped_cash_terminal_minimum_exceeds_half
open Filter Real AvramDividend.Classical
open scoped Topology

theorem AvramDividend.Classical.avram_bvb_obstruction_tenth_clipped_cash_positivepart_cannot_vanish
    (F L : ℕ → ℝ)
    (hF : ∀ n, 4 ≤ n →
      (2 / 25 + 1 / 2 : ℝ) * Real.exp (-(1 / 10 : ℝ)) ≤ F n)
    (hL : ∀ n, L n = 0) :
    ¬ Tendsto (fun n => max (F n - ((1 / 2 : ℝ) + L n)) 0)
      atTop (𝓝 (0 : ℝ)) := by sorry
