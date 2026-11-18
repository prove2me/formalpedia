-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_reusable_power_coloring
-- name    : FasterDistributedMatching.ApproximateMatching.reusable_power_coloring
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T15:38:23.689193+00:00
-- url     : https://prove2.me/theorems/916b8088-6d5f-4d26-916a-850464947f89
-- title:
--   Reusable power-of-line-graph and virtual-copy colors
-- statement:
--   Fix an integer $\ell\ge2$ and a polynomial identifier convention. A deterministic physical LOCAL protocol computes endpoint-consistent colors of the edges such that the power $L(G)^{256\ell+1}$ is properly colored, using at most $\max\{2,\Delta\}^{a\ell}$ colors for an absolute natural exponent $a\ge1$. Its round complexity satisfies
--
--   $$T\le\left\lceil C\ell\max\{1,\log^*n\}\right\rceil$$
--
--   for a positive constant $C$ fixed before all graph inputs. There is also a hosting and routing realization of this power graph whose routes have length at most $256\ell+3$.
--
--   For every valid pairing of active incident edges and every assignment of distinct incident edges to the copies at each creator, combine each assigned edge's color with its endpoint bit. The resulting copy colors use at most twice as many colors and distinguish every two distinct copies whose creators are at physical distance at most $256\ell$.
--
--   This is the coloring and reusable-copy part of Lemma 3.3; the universal operational simulation claims are separate supporting theorems. The construction works uniformly for all later pairings and edge choices.
-- source:
--   Mohsen Ghaffari and Christoph Grunau, Faster Deterministic Distributed Matching: Breaking the Log-Squared Barrier, STOC 2027 submission #1024, Lemma 3.3 and Appendix A, printed pp.9 and 22 / PDF pp.11 and 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing

namespace FasterDistributedMatching.ApproximateMatching
theorem reusable_power_coloring :
    ∀ b : ℕ, ∃ (A : Deterministic (Bounds × ℕ) (Finset ℕ) (ℕ → ℕ)) (C : ℝ) (a : ℕ),
      0 < C ∧ 1 ≤ a ∧
      (∀ k ell, 2 ≤ ell → A.program.rounds (k,ell) ≤ budget C (ell * (logStar k.n : ℝ))) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds) (ell : ℕ),
        2 ≤ ell → boundedGraph G k.n k.degree →
        ∀ ids : Fin N → ℕ, Identifiers k.n (b + 1) ids →
          ∃ chi : Sym2 (Fin N) → ℕ,
            (∀ u v, G.Adj u v →
              execute A G (k,ell) ids (neighborIDs G ids) u (ids v) = chi s(u,v) ∧
              execute A G (k,ell) ids (neighborIDs G ids) v (ids u) = chi s(u,v)) ∧
            Proper (graphPower (lineGraph G) (256 * ell + 1))
              ((max 2 k.degree) ^ (a * ell)) (fun e => chi e.val) ∧
            (∃ D : Routed G G.edgeSet,
              D.graph = graphPower (lineGraph G) (256 * ell + 1) ∧
              (∀ e : G.edgeSet, D.owner e ∈ e.val) ∧ RouteLength D (256 * ell + 3)) ∧
            ∀ (x : Sym2 (Fin N) → ℝ) (q : ℝ) (p : Pairing N),
              ValidPairing G x q p → ∀ pick : Copy p → Fin N, CopyEdgeChoice G p pick →
                ReusableColors G ell (2 * (max 2 k.degree) ^ (a * ell)) (copyColor ids chi pick) := by sorry
end FasterDistributedMatching.ApproximateMatching
