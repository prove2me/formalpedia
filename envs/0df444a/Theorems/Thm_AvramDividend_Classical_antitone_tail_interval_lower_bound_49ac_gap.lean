-- Prove2me | Theorems.Thm_AvramDividend_Classical_antitone_tail_interval_lower_bound_49ac_gap
-- name    : AvramDividend.Classical.antitone_tail_interval_lower_bound_49ac_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:47:31.045779+00:00
-- url     : https://prove2.me/theorems/85620559-63de-40cc-8b2a-44daf79d222f
-- title:
--   Antitone tail lower-bounds its interval integral
-- statement:
--   Let T be antitone on (0,inf) and continuous on the closed segment [x/2, x] for some x > 0. Then the endpoint value times the half-length lower-bounds the interval integral: T(x) * (x - x/2) <= integral of T over [x/2, x]. This is the deterministic quantitative step behind the finite-positive-tail consequence used on the unbounded Esscher excursion route: with a finite extended integral over [x/2, x], antitonicity forces T(x) < infinity.
-- source:
--   Deterministic real-analysis step supporting AvramDividend.Classical.unbounded_esscher_excursion_integrated_scale_representation (49acdc06): the finite-tail consequence recorded in the Esscher-to-excursion transfer notes (Chan-Kyprianou-Savov tail monotonicity). Pure Mathlib interval-integral monotonicity; no excursion measure.

import Mathlib
open MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.antitone_tail_interval_lower_bound_49ac_gap
    (T : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hTcont : ContinuousOn T (uIcc (x / 2) x))
    (hTanti : AntitoneOn T (Ioi (0 : ℝ))) :
    T x * (x - x / 2) ≤ ∫ t in (x / 2)..x, T t := by sorry
