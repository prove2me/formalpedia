-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_lemma_4_2
-- name    : BipartiteVRM.Competitive.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:44.232209+00:00
-- url     : https://prove2.me/theorems/d165e74b-d0d0-464e-80c9-ddc5ae184054
-- title:
--   Lemma 4.2 — edge disjointness and arrived interior vertices
-- statement:
--   Fix $\gamma>1$, any causal deterministic tie rule, and a minimum-TA-cost perfect matching $M^*$ independently of the VRM run. At any time $t\ge0$, different free requests have edge-disjoint optimal paths, and every interior vertex of each optimal path has arrived:
--
--   $$r\ne p\ \Longrightarrow\ E(P_r^*(t))\cap E(P_p^*(t))=\varnothing,\qquad
--   v\text{ interior to }P_r^*(t)\ \Longrightarrow\ a_v\le t.$$
--
--   Both requests in the first clause are free at $t$. Interior excludes the two endpoints. The terminal server can be unarrived, and paths are not prematurely restricted to the arrived graph. These properties justify the per-edge charging construction.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the RA, SA and AU execution with an arbitrary fixed tie rule → unbounded iteration of the explicit event transition with cached simple minimum paths and a fixed View-only selector over nonempty finite choices; reason: the local rule sees only received arrival times, distances and its history; the environment advances the real clock and reveals arrivals; termination and feasible completion are conclusions, not fields or hypotheses
--   - encoding: the path component of M_t symmetric-difference Mstar containing a free request → the ordered walk which follows an Mstar edge forward and an M_t edge backward, with an analysis bound of size plus one iterations; reason: optimal_path_component concludes that this computes the whole component; the terminal server need not have arrived
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 10, Lemma 4.2

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-- Lemma 4.2, p. 10: both disjointness and arrival of every interior vertex. -/
theorem lemma_4_2 {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) (Mstar : Matching)
    (hMstar : IsOptimal I Mstar) (t : ℝ) (ht : 0 ≤ t) :
    (∀ r ∈ freeAt I γ tie t, ∀ p ∈ freeAt I γ tie t, r ≠ p →
      Disjoint (pathEdges (optimalPath I γ tie Mstar t r))
        (pathEdges (optimalPath I γ tie Mstar t p))) ∧
    (∀ r ∈ freeAt I γ tie t, ∀ v ∈ (optimalPath I γ tie Mstar t r).dropLast.tail,
      I.arrival v ≤ t) := by sorry

end BipartiteVRM.Competitive
