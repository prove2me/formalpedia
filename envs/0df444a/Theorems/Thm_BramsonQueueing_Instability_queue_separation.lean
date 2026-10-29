-- Prove2me | Theorems.Thm_BramsonQueueing_Instability_queue_separation
-- name    : BramsonQueueing.Instability.queue_separation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:20:49.727835+00:00
-- url     : https://prove2.me/theorems/71694f7f-b5d5-416e-a9b6-58fc523ea607
-- title:
--   Equation (3.6) — high-priority queues separate after a finite hitting time
-- statement:
--   For the random Lu–Kumar network with arbitrary positive service means and any finite initial queue vector, let $\tau_0$ be the first nonnegative time when class 2 or class 4 is empty. Almost surely,
--   $$\tau_0<\infty,\qquad Z_2(t)=0\ \text{or}\ Z_4(t)=0\quad\text{for every }t\ge\tau_0.$$
--   Finiteness is part of the conclusion, as asserted immediately before (3.6). The same probability-one event covers every real time after the hitting time. This records the occupation restriction used by the service-exclusion lemma.
--
--   Differences from the source:
--   - encoding: classes 1–4 and stations 1–2 → Fin 4 and Fin 2, indexed from zero; reason: subtracting one from each label preserves all routes, means, and priority comparisons
--   - encoding: the random network on its probability space → an arbitrary probability space carrying the specified primitives and its queue-conserving service-clock trajectories; reason: this is a realization of the source process, with no restriction on its law or queue lengths
--   - encoding: the first empty-high-priority-queue time, possibly infinite before finiteness is proved → the infimum in nonnegative extended reals, with finiteness in the conclusion; reason: the empty hitting set has infimum infinity and the event quantifies over all nonnegative real times
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), DOI 10.1007/978-3-540-68896-9, Equation (3.6) and preceding finiteness assertion, printed 57 / PDF 65

import Mathlib
import Definitions.Def_BramsonQueueing_Instability_LuKumarRun

namespace BramsonQueueing.Instability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Equation (3.6) and the preceding almost-sure finiteness assertion. -/
theorem queue_separation {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {d : LuKumarParameters} {p : LuKumarPrimitives Ω d}
    {z₀ : Fin 4 → ℕ} (r : LuKumarRun p z₀) :
    ∀ᵐ ω, tauZero r ω < ⊤ ∧
      ∀ t : ℝ, 0 ≤ t → tauZero r ω ≤ ENNReal.ofReal t →
        r.Z t ω 1 = 0 ∨ r.Z t ω 3 = 0 := by sorry

end BramsonQueueing.Instability
