-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_eventual_uniform_positive_cash_gap_refutes_zero_limit
-- name    : AvramDividend.Classical.avram_bvb_obstruction_eventual_uniform_positive_cash_gap_refutes_zero_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:45:03.568566+00:00
-- url     : https://prove2.me/theorems/1453dade-b416-4154-a516-bcfa9c1ab8bc
-- title:
--   Uniform eventual positive original stopped-cash gap refutes vanishing positive-part physical error
-- statement:
--   If a real physical-grid cash excess A_n is bounded below by a fixed ε>0 for every mesh index n≥4, its positive part max(A_n,0) cannot converge to zero. This is the final deterministic contradiction needed to disprove a pathwise original BV drift-only cash budget without proving an unnecessarily strong cash-sequence limit.
-- source:
--   Tendsto to zero forces the positive part eventually below ε in the neighbourhood Iio ε, whereas the source exact finite-grid discounted Stieltjes cash lower bound forces it above ε for all n≥4. The two eventual properties contradict each other.

import Mathlib
open Filter Set
open scoped Topology

theorem AvramDividend.Classical.avram_bvb_obstruction_eventual_uniform_positive_cash_gap_refutes_zero_limit (A : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hLower : ∀ n, 4 ≤ n → ε ≤ A n) :
    ¬ Tendsto (fun n => max (A n) 0) atTop (𝓝 (0 : ℝ)) := by sorry
