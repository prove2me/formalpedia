-- Prove2me | Theorems.Thm_BramsonQueueing_Instability_random_lu_kumar_unstable
-- name    : BramsonQueueing.Instability.random_lu_kumar_unstable
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:20:55.4134+00:00
-- url     : https://prove2.me/theorems/378af8a9-6c12-4eec-a984-e7e6bda3e8b9
-- title:
--   Theorem 3.2 — instability of the random Lu–Kumar network
-- statement:
--   Consider the random Lu–Kumar network: rate-one Poisson arrivals follow route $1\to2\to3\to4\to\mathrm{exit}$, stations serve classes $\{1,4\}$ and $\{2,3\}$, and the preemptive priorities are 4 over 1 and 2 over 3. All service requirements are independent exponentials with arbitrary positive means $m_1,m_2,m_3,m_4$. If $m_2+m_4>1$, the network is unstable in the source's stochastic sense:
--   $$\exists z_0\in\mathbb N^4:\quad\mathbb P_{z_0}\!\left(\sum_{k=1}^4Z_k(t)\longrightarrow\infty\text{ as real }t\to\infty\right)>0.$$
--   The conclusion is escape of the total number of jobs with positive probability from some initial state. No subcritical load inequalities or equality of service means are imposed. This is the stochastic capstone of the mission.
--
--   Differences from the source:
--   - encoding: classes 1–4 and stations 1–2 → Fin 4 and Fin 2, indexed from zero; reason: subtracting one from each label preserves all routes, means, and priority comparisons
--   - encoding: the random network on its probability space → an arbitrary probability space carrying the specified primitives and its queue-conserving service-clock trajectories; reason: this is a realization of the source process, with no restriction on its law or queue lengths
--   - encoding: a process law for each finite queue-length initial state → a family of queue-conserving runs on common primitive randomness; reason: common independent service sequences realize all countably many initial states without imposing relations on their laws
--   - encoding: probability of the escape event → the ambient measure evaluated on that event, using its outer-measure extension; reason: right-continuity identifies the event up to a null set with a measurable rational-time event, so this equals probability in the completed space
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), DOI 10.1007/978-3-540-68896-9, Theorem 3.2, printed 56 / PDF 64; instability definition printed 53–54 / PDF 61–62

import Mathlib
import Definitions.Def_BramsonQueueing_Instability_LuKumarRun

namespace BramsonQueueing.Instability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Theorem 3.2: stochastic escape, with all four service means positive. -/
theorem random_lu_kumar_unstable
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {d : LuKumarParameters} {p : LuKumarPrimitives Ω d}
    (runs : ∀ z₀ : Fin 4 → ℕ, LuKumarRun p z₀)
    (h : 1 < d.m 1 + d.m 3) :
    ∃ z₀ : Fin 4 → ℕ, 0 < ℙ {ω | Tendsto
      (fun t : ℝ => ∑ k : Fin 4, ((runs z₀).Z t ω k : ℝ)) atTop atTop} := by sorry

end BramsonQueueing.Instability
