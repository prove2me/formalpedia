-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_lemma_3_1
-- name    : BipartiteVRM.Competitive.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:10.712633+00:00
-- url     : https://prove2.me/theorems/10288f62-0005-4997-9378-b7e038d66e3f
-- title:
--   Lemma 3.1 — no negative cycle in any reachable state
-- statement:
--   Let $\gamma>1$, and fix any causal deterministic tie rule for VRM. At every state reachable on a finite balanced input in any metric space, the residual graph $H$ has no negative directed cycle:
--
--   $$\operatorname{weight}(C)\ge0\qquad\text{for every directed cycle }C\text{ in }H.$$
--
--   Unmatched forward edges have weight $\gamma D(e)$; matched reverse edges have weight $-D(e)$. Every event state, including those between events with equal timestamps, is covered. This is the invariant that validates the signed shortest-path search; it is not assumed in the execution model.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the RA, SA and AU execution with an arbitrary fixed tie rule → unbounded iteration of the explicit event transition with cached simple minimum paths and a fixed View-only selector over nonempty finite choices; reason: the local rule sees only received arrival times, distances and its history; the environment advances the real clock and reveals arrivals; termination and feasible completion are conclusions, not fields or hypotheses
--   - encoding: augmenting paths and a minimum net cost, with infinity if none exists → simple ordered vertex lists, their finite edge sets and a WithTop real minimum, using top on the empty path set; reason: simple paths suffice by Lemma 3.1, negative weights remain signed, and finite enumeration has no unbounded-infimum default
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 7, Lemma 3.1; p. 25, Appendix A

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-- Lemma 3.1, p. 7; proof Appendix A, p. 25. Every reachable event state is
included, with no generic-position or favorable-tie assumption. -/
theorem lemma_3_1 {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) (n : ℕ) :
    ∀ C : List Vertex, DirectedCycle (state I γ tie n).inserted (state I γ tie n).off C →
      0 ≤ cycleWeight (edgeDistance I) γ C := by sorry

end BipartiteVRM.Competitive
