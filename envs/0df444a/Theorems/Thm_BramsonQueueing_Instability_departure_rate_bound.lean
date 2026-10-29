-- Prove2me | Theorems.Thm_BramsonQueueing_Instability_departure_rate_bound
-- name    : BramsonQueueing.Instability.departure_rate_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:20:42.45503+00:00
-- url     : https://prove2.me/theorems/4ddb20e8-31c3-4b6e-b552-747ea392c91f
-- title:
--   Equation (3.7) — exact almost-sure departure-rate bound
-- statement:
--   For the random Lu–Kumar network, with arbitrary positive means $m_1,m_2,m_3,m_4$ and any finite initial queue vector, let $D(t)$ count departures from the network over $(0,t]$. Almost surely,
--   $$\limsup_{t\to\infty}\frac{D(t)}{t}\le\frac1{m_2+m_4}.$$
--   Time ranges over the reals. Initially present jobs are allowed without changing the constant, and neither subcriticality nor $m_2+m_4>1$ is needed for this milestone. The bound supplies the departure-rate component of the instability statement.
--
--   Differences from the source:
--   - encoding: classes 1–4 and stations 1–2 → Fin 4 and Fin 2, indexed from zero; reason: subtracting one from each label preserves all routes, means, and priority comparisons
--   - encoding: the random network on its probability space → an arbitrary probability space carrying the specified primitives and its queue-conserving service-clock trajectories; reason: this is a realization of the source process, with no restriction on its law or queue lengths
--   - encoding: limsup of the real-time departure ratio is at most 1/(m₂+m₄) → for every positive epsilon, the same bound plus epsilon holds for every sufficiently large positive real time; reason: this is the equivalent epsilon-tail definition and avoids a default real limsup for an unbounded function
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), DOI 10.1007/978-3-540-68896-9, Equation (3.7), printed 58 / PDF 66

import Mathlib
import Definitions.Def_BramsonQueueing_Instability_LuKumarRun

namespace BramsonQueueing.Instability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Equation (3.7), in the equivalent epsilon-tail form of its limsup bound. -/
theorem departure_rate_bound {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {d : LuKumarParameters} {p : LuKumarPrimitives Ω d}
    {z₀ : Fin 4 → ℕ} (r : LuKumarRun p z₀) :
    ∀ᵐ ω, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
      ∀ t : ℝ, T ≤ t → 0 < t →
        (departures r.toQueueingPaths t ω : ℝ) / t ≤ 1 / (d.m 1 + d.m 3) + ε := by sorry

end BramsonQueueing.Instability
