-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_Supplement_lemma_5_6
-- name    : BipartiteVRM.Competitive.Supplement.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:32:00.717913+00:00
-- url     : https://prove2.me/theorems/d0b758ba-53dc-472b-a679-8832639482b0
-- title:
--   Lemma 5.6 — total cost at most $\frac{2\gamma}{\gamma-1}$ times the total waiting time
-- statement:
--   Fix $\gamma>1$, any tie rule and any MPMD input with $|R|=2m$ in any metric space. Let $\mathrm{ALG}$ be the cost of the output, distance plus the waiting time of both requests of every output pair, and let $W_R=\sum_{r\in R}(t_r-a_r)$ be the total waiting time of all requests, $t_r$ being the time $r$ is matched. Then
--
--   $$\mathrm{ALG}\le\frac{2\gamma}{\gamma-1}\,W_R.$$
--
--   This is the first half of the proof of Theorem 5.1; unlike its bipartite counterpart Lemma 4.1 it carries no additive $2$, because $W_R$ counts both endpoints of every pair.
--
--   Differences from the source:
--   - encoding: a finite request set R with |R| = 2m in any metric space, locations and arrival times a_v ≥ 0 that may coincide → the published MatchingDelays.Linear.Instance n X (labels 0..n−1 in nondecreasing arrival order, any MetricSpace X) with Even n, m = n/2; reason: every finite input can be relabeled in arrival order (simultaneous arrivals in any order); labels give the algorithm no future data, and repeated locations and arrival times are allowed
--   - encoding: an arbitrary but fixed rule for ties among simultaneous events and among the choices of N_uv and v in Steps 1 and 2 → every TieRule, a View-and-history selector over the nonempty finite option sets; reason: the rule sees only received data and its own history; every statement quantifies over all such rules
--   - encoding: W_R = Σ_{r∈R} (t_r − a_r) → the sum over output pairs uv at time t of (t − a_u) + (t − a_v); reason: the output is a perfect matching in which each request appears exactly once (Theorem 5.1's feasibility conclusion), so the two sums are the same
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 17, Lemma 5.6; W_R defined on p. 16, §5.3

import Definitions.Def_BipartiteVRM_Competitive_Supplement_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive.Supplement

open MatchingDelays.Linear (Instance Edge)

/-- Lemma 5.6, p. 17: no additive 2, both endpoints' waiting in W_R. -/
theorem lemma_5_6 {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X) (hn : Even n)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) :
    ALG I γ tie ≤ 2 * γ / (γ - 1) * totalWaiting I γ tie := by sorry

end BipartiteVRM.Competitive.Supplement
