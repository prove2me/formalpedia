-- Prove2me | Theorems.Thm_BramsonQueueing_Instability_no_simultaneous_service
-- name    : BramsonQueueing.Instability.no_simultaneous_service
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:20:34.282116+00:00
-- url     : https://prove2.me/theorems/252095a9-d31f-4c4a-8840-ed5a1606bd3b
-- title:
--   Lemma 3.3 — no simultaneous service at classes 2 and 4
-- statement:
--   For the random Lu–Kumar network with arbitrary positive service means and any finite initial queue vector, define $\tau_0$ as the first time either class 2 or class 4 is empty. Let $u_k(t)$ denote the instantaneous allocated service rate under the preemptive priority rule. Almost surely,
--   $$\tau_0<\infty,\qquad \neg\bigl(u_2(t)>0\text{ and }u_4(t)>0\bigr)\quad\text{for every }t\ge\tau_0.$$
--   Thus these two classes are not served simultaneously at any later time, on a single probability-one event. The source's preceding finiteness assertion is included explicitly, rather than assumed. The statement concerns actual service in the stochastic network.
--
--   Differences from the source:
--   - encoding: classes 1–4 and stations 1–2 → Fin 4 and Fin 2, indexed from zero; reason: subtracting one from each label preserves all routes, means, and priority comparisons
--   - encoding: the random network on its probability space → an arbitrary probability space carrying the specified primitives and its queue-conserving service-clock trajectories; reason: this is a realization of the source process, with no restriction on its law or queue lengths
--   - encoding: the first empty-high-priority-queue time, possibly infinite before finiteness is proved → the infimum in nonnegative extended reals, with finiteness in the conclusion; reason: the empty hitting set has infimum infinity and the event quantifies over all nonnegative real times
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), DOI 10.1007/978-3-540-68896-9, Lemma 3.3 and preceding finiteness assertion, printed 57 / PDF 65

import Mathlib
import Definitions.Def_BramsonQueueing_Instability_LuKumarRun

namespace BramsonQueueing.Instability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Lemma 3.3, including finiteness of the hitting time defined before it. -/
theorem no_simultaneous_service {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {d : LuKumarParameters} {p : LuKumarPrimitives Ω d}
    {z₀ : Fin 4 → ℕ} (r : LuKumarRun p z₀) :
    ∀ᵐ ω, tauZero r ω < ⊤ ∧
      ∀ t : ℝ, 0 ≤ t → tauZero r ω ≤ ENNReal.ofReal t →
        ¬ (0 < serviceRate (r.Z t ω) 1 ∧ 0 < serviceRate (r.Z t ω) 3) := by sorry

end BramsonQueueing.Instability
