-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_Supplement_lemma_5_8
-- name    : BipartiteVRM.Competitive.Supplement.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:33:29.975139+00:00
-- url     : https://prove2.me/theorems/29ebd48a-bbe9-4485-8145-382f44b5c4a4
-- title:
--   Lemma 5.8 — both optimal-path age bounds in the non-bipartite case
-- statement:
--   Fix $\gamma>1$, any tie rule, an MPMD input with $|R|=2m$ and any minimum-cost perfect matching $M^*$ on $R$ under $D$. Let $t$ be a stable time and $u$ a free request at $t$ such that the terminal request of $P^*=P^*_u(t)$ has arrived by $t$, and let $D^*=D(P^*\cap M^*)$. Then
--
--   $$D^*\ge\operatorname{age}(u,t)\qquad\text{and}\qquad D^*\ge\frac{\operatorname{age}(z,t)}{\gamma+1}\ \text{for every vertex } z \text{ of } P^*,$$
--
--   where $\operatorname{age}(v,t)=t-a_v$.
--
--   These bounds make the Case 2 charge rates well defined and bound how long an edge of $M^*$ can be charged.
--
--   Differences from the source:
--   - encoding: a finite request set R with |R| = 2m in any metric space, locations and arrival times a_v ≥ 0 that may coincide → the published MatchingDelays.Linear.Instance n X (labels 0..n−1 in nondecreasing arrival order, any MetricSpace X) with Even n, m = n/2; reason: every finite input can be relabeled in arrival order (simultaneous arrivals in any order); labels give the algorithm no future data, and repeated locations and arrival times are allowed
--   - encoding: an arbitrary but fixed rule for ties among simultaneous events and among the choices of N_uv and v in Steps 1 and 2 → every TieRule, a View-and-history selector over the nonempty finite option sets; reason: the rule sees only received data and its own history; every statement quantifies over all such rules
--   - encoding: a stable time t (no request arrives and no augmentation is performed at t) → 0 ≤ t, no arrival at t and no output pair with time t; reason: for t < 0 there is no free request, so the condition 0 ≤ t excludes only vacuous cases
--   - encoding: the optimal path P*_u(t), its terminal request and D* = D(P* ∩ M*) → the vertex list optimalWalk from u, its last element, and the sum of TA distances over its edges in M*; reason: the walk traverses the component of M_t △ M* containing u
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 18, Lemma 5.8

import Definitions.Def_BipartiteVRM_Competitive_Supplement_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive.Supplement

open MatchingDelays.Linear (Instance Edge)

/-- Lemma 5.8, p. 18: both bounds, the second at every vertex of P*. -/
theorem lemma_5_8 {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X) (hn : Even n)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) (Mstar : Matching) (hMstar : IsOptimal I Mstar)
    (t : ℝ) (ht : stable I γ tie t) (u : ℕ) (hu : u ∈ freeAt I γ tie t)
    (hterm : ∃ v, (optimalPath I γ tie Mstar t u).getLast? = some v ∧
      MatchingDelays.Linear.arrival I v ≤ t) :
    age I u t ≤ optimalLength I γ tie Mstar t u ∧
      ∀ z ∈ optimalPath I γ tie Mstar t u,
        age I z t / (γ + 1) ≤ optimalLength I γ tie Mstar t u := by sorry

end BipartiteVRM.Competitive.Supplement
