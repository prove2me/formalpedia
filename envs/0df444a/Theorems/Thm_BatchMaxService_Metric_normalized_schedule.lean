-- Prove2me | Theorems.Thm_BatchMaxService_Metric_normalized_schedule
-- name    : BatchMaxService.Metric.normalized_schedule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:24:18.067112+00:00
-- url     : https://prove2.me/theorems/785058ab-f87c-479a-a975-e7323a84dc14
-- title:
--   Proposition 3.1 — normalization into complete arrival blocks
-- statement:
--   Let $I$ be a finite real-time input on a known finite metric and $\sigma$ any feasible elective schedule, including arbitrary repositioning and separately billed same-time events. There exists a feasible schedule $\tau$ whose nonempty batches are consecutive blocks of complete arrival epochs, each served at its final epoch time, such that
--
--   $$\operatorname{Mov}(\tau)\le\operatorname{Mov}(\sigma),\qquad\operatorname{Delay}(\tau)\le\operatorname{Delay}(\sigma).$$
--
--   The two objective components are dominated separately. Normalization is a conclusion, and is not a restriction on the competitors defining OPT.
--
--   Differences from the source:
--   - encoding: a known nonempty finite metric and finitely many distinct request labels → sites Fin n with an arbitrary MetricSpace, an initial site, and a finite subset of natural labels; reason: every such metric and finite identity set can be enumerated, preserving all real distances, arrivals and repeated location/time pairs
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), Proposition 3.1, printed p. 5 / PDF p. 6

import Mathlib
import Definitions.Def_BatchMaxService_Metric_RequestInput

namespace BatchMaxService.Metric

/-- Proposition 3.1, printed p. 5 / PDF 6. Separate domination, complete epochs,
    and the last-epoch service timestamp are all retained. -/
theorem normalized_schedule {n : ℕ} [MetricSpace (Fin n)] (I : RequestInput n)
    (σ : Schedule n) (hσ : Feasible I σ) :
    ∃ τ : Schedule n, Feasible I τ ∧ Normalized I τ ∧
      movement τ ≤ movement σ ∧ delay I τ ≤ delay I σ := by sorry

end BatchMaxService.Metric
