-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_strict_prefix_integral_closed_minus_atom
-- name    : AvramDividend.Classical.avram_chat24_strict_prefix_integral_closed_minus_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:56:52.187988+00:00
-- url     : https://prove2.me/theorems/e3634d0d-ce4a-4bbd-b4d5-86422d3e98fd
-- title:
--   Dominated strict-prefix convergence equals stopped integral minus endpoint fiber
-- statement:
--   General deterministic measure-theoretic ingredient of a66ab8c0. If the stopped kernel is integrable and strict prefix clocks converge to a finite clock, dominated convergence gives the strict prefix integral. The difference from the closed stopped integral is exactly the endpoint fiber, using integrable indicators and integral_add. No original-process hypotheses are assumed or altered.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_strict_prefix_integral_closed_minus_atom
    {α : Type*} [MeasurableSpace α] (m : Measure α)
    (clock : α → ℝ≥0) (hc : Measurable clock)
    (f : α → ℝ) (t : ℝ≥0)
    (hf : Integrable (fun a => if clock a ≤ t then f a else 0) m)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < t)
    (hl : Tendsto u atTop (nhds t)) :
    Tendsto (fun n => ∫ a, if clock a ≤ u n then f a else 0 ∂m) atTop
      (nhds ((∫ a, if clock a ≤ t then f a else 0 ∂m) -
        ∫ a, if clock a = t then f a else 0 ∂m)) := by sorry
