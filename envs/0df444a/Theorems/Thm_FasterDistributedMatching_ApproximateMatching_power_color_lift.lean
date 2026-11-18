-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_power_color_lift
-- name    : FasterDistributedMatching.ApproximateMatching.power_color_lift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T15:52:41.497275+00:00
-- url     : https://prove2.me/theorems/e1074e4d-7c19-4861-aad0-3977f717e699
-- title:
--   Routing and virtual-copy separation from line-power colors
-- statement:
--   Let $G$ be a finite simple graph with injective vertex identifiers, let $\ell,K$ be natural numbers, and let $\chi$ be a proper $K$-coloring of $L(G)^{256\ell+1}$. Then this power graph has an endpoint-hosted routing realization with physical routes of length at most $256\ell+3$.
--
--   For every family of virtual copies, assign each copy an incident physical edge, with distinct assigned edges for copies at a common creator. Color a copy by twice its assigned edge color plus the bit identifying its endpoint, ordered by identifiers. These colors satisfy
--
--   $$\text{color}(a)<2K,\qquad a\ne b,\ \operatorname{dist}_G(\operatorname{creator}(a),\operatorname{creator}(b))\le256\ell\ \Longrightarrow\ \text{color}(a)\ne\text{color}(b).$$
--
--   This separates the routing and copy-separation argument from the protocol that computes the edge colors, so it can be reused for every later active-edge pairing. Compared with the source's setting $\ell\ge2$, the geometric statement also admits $\ell=0,1$; no step of the transfer argument requires the lower bound. Validity of an active-edge pairing is unnecessary once the distinct incident-edge choices are supplied.
-- source:
--   Mohsen Ghaffari and Christoph Grunau, Faster Deterministic Distributed Matching: Breaking the Log-Squared Barrier, STOC 2027 submission #1024, Lemma 3.3 and Appendix A, printed pp.9 and 22 / PDF pp.11 and 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing

namespace FasterDistributedMatching.ApproximateMatching
theorem power_color_lift (N : ℕ) (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (ell K : ℕ) (chi : Sym2 (Fin N) → ℕ)
    (hchi : Proper (graphPower (lineGraph G) (256*ell+1)) K (fun e => chi e.val)) :
    (∃ D : Routed G G.edgeSet,
      D.graph = graphPower (lineGraph G) (256*ell+1) ∧
      (∀ e : G.edgeSet, D.owner e ∈ e.val) ∧ RouteLength D (256*ell+3)) ∧
    ∀ (p : Pairing N) (pick : Copy p → Fin N), CopyEdgeChoice G p pick →
      ReusableColors G ell (2*K) (copyColor ids chi pick) := by sorry
end FasterDistributedMatching.ApproximateMatching
