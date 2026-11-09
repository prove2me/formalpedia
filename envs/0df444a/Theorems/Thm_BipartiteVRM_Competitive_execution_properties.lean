-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_execution_properties
-- name    : BipartiteVRM.Competitive.execution_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:22.882638+00:00
-- url     : https://prove2.me/theorems/2889e1a2-68d0-454a-a526-ef40fb610f0a
-- title:
--   §3.3 — deterministic online feasible completion for every tie rule
-- statement:
--   For every $\gamma>1$ and every fixed causal tie rule, the explicit RA/SA/AU execution is unique, eventually halts with a feasible perfect matching, maintains equal saturated sets in its auxiliary and output matchings, keeps every cached path minimum, and never revises an output decision. Across any two metric inputs whose observed data agree through $t$, its decisions through $t$ agree:
--
--   $$\operatorname{Obs}_{\le t}(I)=\operatorname{Obs}_{\le t}(J)
--   \ \Longrightarrow\ \operatorname{Out}_{\le t}(I)=\operatorname{Out}_{\le t}(J).$$
--
--   The inputs in this comparison may have different final sizes and different ambient metric spaces. Only labels, arrivals, and distances between already arrived items need agree. Thus the execution uses neither the ambient metric nor $m$ in advance. The empty input is included. These are source execution properties used by the main theorem, not assumed invariants of a supplied run.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the RA, SA and AU execution with an arbitrary fixed tie rule → unbounded iteration of the explicit event transition with cached simple minimum paths and a fixed View-only selector over nonempty finite choices; reason: the local rule sees only received arrival times, distances and its history; the environment advances the real clock and reveals arrivals; termination and feasible completion are conclusions, not fields or hypotheses
--   - encoding: deterministic online execution and no prior knowledge of the metric space or m → uniqueness of the explicit transition recurrence, feasible halting and prefix equality across different metric spaces and final counts; reason: this spells out all online clauses using only the observations allowed in §2.1
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), pp. 8–9, §3.3–§3.4; p. 6, §2.1

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

universe uVRMproperties

namespace BipartiteVRM.Competitive

/-- §3.3–§3.4, pp. 8–9: eventual feasible perfect output, immutable decisions,
deterministic execution, and dependence only on observed distances and arrivals. -/
theorem execution_properties (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) :
    Causal.{uVRMproperties, uVRMproperties} γ tie ∧ ∀ {X : Type uVRMproperties} [MetricSpace X] (I : Input X),
      ExecutionCorrect I γ tie := by sorry

end BipartiteVRM.Competitive
