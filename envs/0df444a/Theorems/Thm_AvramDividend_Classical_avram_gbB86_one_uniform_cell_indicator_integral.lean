-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB86_one_uniform_cell_indicator_integral
-- name    : AvramDividend.Classical.avram_gbB86_one_uniform_cell_indicator_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:58:58.663202+00:00
-- url     : https://prove2.me/theorems/86ccea79-3dfa-46d5-abb9-7dcd7716c7dc
-- title:
--   One uniform half-open cell indicator has exactly cell-width integral
-- statement:
--   The open-horizon Lebesgue integral of a constant multiplied by the indicator of one half-open uniform partition cell is the cell width times the constant. The initial and final endpoints have measure zero.
-- source:
--   Scalar interval-integration atom for finite-step time integral B85 and exact deterministic two-grid overlap B78.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB86_one_uniform_cell_indicator_integral
    (n N r : ℕ) (hn : 0 < n) (hN : 0 < N) (hr : r < N) (a : ℝ) :
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then a else 0) ∂volume) = δ * a := by sorry
