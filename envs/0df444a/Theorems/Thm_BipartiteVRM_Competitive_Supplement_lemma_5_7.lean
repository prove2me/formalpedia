-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_Supplement_lemma_5_7
-- name    : BipartiteVRM.Competitive.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:32:32.670668+00:00
-- url     : https://prove2.me/theorems/ec05faae-3d9b-415d-8c4d-f1db4f2cd4d0
-- title:
--   Lemma 5.7 — optimal paths of two free requests coincide or share no edge; interiors have arrived
-- statement:
--   Fix $\gamma>1$, any tie rule, an MPMD input with $|R|=2m$, any minimum-cost perfect matching $M^*$ on $R$ under $D$, and a time $t$. Let $u$ and $w$ be distinct free requests at time $t$.
--
--   1. If $w$ is the terminal request of $P^*_u(t)$, then $P^*_u(t)$ and $P^*_w(t)$ have the same edges.
--   2. Otherwise $P^*_u(t)$ and $P^*_w(t)$ share no edge.
--   3. Every interior vertex of the optimal path of a free request at time $t$ has arrived by $t$.
--
--   This governs the charging scheme of §5.4: at most two requests, the two ends of one optimal path, charge an edge of $M^*$ at the same time.
--
--   Differences from the source:
--   - encoding: a finite request set R with |R| = 2m in any metric space, locations and arrival times a_v ≥ 0 that may coincide → the published MatchingDelays.Linear.Instance n X (labels 0..n−1 in nondecreasing arrival order, any MetricSpace X) with Even n, m = n/2; reason: every finite input can be relabeled in arrival order (simultaneous arrivals in any order); labels give the algorithm no future data, and repeated locations and arrival times are allowed
--   - encoding: an arbitrary but fixed rule for ties among simultaneous events and among the choices of N_uv and v in Steps 1 and 2 → every TieRule, a View-and-history selector over the nonempty finite option sets; reason: the rule sees only received data and its own history; every statement quantifies over all such rules
--   - encoding: the optimal path P*_u(t), the component of M_t △ M* containing u, its terminal request and interior vertices → the vertex list optimalWalk of M_t = stateAt t and M* from u, its last element and its dropLast.tail; same edges as equality of edge sets; reason: the walk alternately follows the M*-edge and the M_t-edge and so traverses that component; the fuel n + 1 never truncates it
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 17, Lemma 5.7; definition of P*_u(t), p. 17

import Definitions.Def_BipartiteVRM_Competitive_Supplement_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive.Supplement

open MatchingDelays.Linear (Instance Edge)

/-- Lemma 5.7, p. 17: same edges or no shared edge, and arrived interiors. -/
theorem lemma_5_7 {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X) (hn : Even n)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) (Mstar : Matching) (hMstar : IsOptimal I Mstar)
    (t : ℝ) :
    (∀ u ∈ freeAt I γ tie t, ∀ w ∈ freeAt I γ tie t, u ≠ w →
      ((optimalPath I γ tie Mstar t u).getLast? = some w →
        pathEdges (optimalPath I γ tie Mstar t u) =
          pathEdges (optimalPath I γ tie Mstar t w)) ∧
      ((optimalPath I γ tie Mstar t u).getLast? ≠ some w →
        Disjoint (pathEdges (optimalPath I γ tie Mstar t u))
          (pathEdges (optimalPath I γ tie Mstar t w)))) ∧
    (∀ u ∈ freeAt I γ tie t, ∀ z ∈ (optimalPath I γ tie Mstar t u).dropLast.tail,
      MatchingDelays.Linear.arrival I z ≤ t) := by sorry

end BipartiteVRM.Competitive.Supplement
