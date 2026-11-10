-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_3
-- name    : FasterDistributedMatching.ApproximateMatching.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:14:02.331303+00:00
-- url     : https://prove2.me/theorems/f98272df-d005-4ca3-94fd-11e76b7e0e24
-- title:
--   Lemma 3.3 — reusable power-of-line-graph coloring
-- statement:
--   Let $G$ have known vertex and degree bounds $n,\Delta$, let $\ell\ge2$ be an integer, and set $R=256\ell$. A deterministic LOCAL protocol computes at both endpoints the same color for each physical edge. There are uniform constants $C>0$ and an integer $a\ge1$ such that
--
--   $$\#\text{colors}\le\max\{2,\Delta\}^{a\ell},\qquad T\le\lceil C\ell\max\{1,\log^*n\}\rceil,$$
--
--   and the edge colors properly color $L(G)^{R+1}$. For every later pairing of active edges, assign each copy an incident physical edge, distinct among copies at one creator. Its edge color and endpoint bit give fewer than twice as many copy colors, distinguishing any two copies whose creators are within distance $R$, including different copies of one creator.
--
--   One power-graph round is operationally simulable in $O(\ell)$ physical rounds from physical neighbors and hosted incident-edge data alone. Bounded physical routes of length at most $R+3$ for that power graph also exist. Any finite auxiliary protocol with supplied routes of length $r$ is simulable with physical time at most $C'(r+1)$ times its round count; the simulator rules precede all graphs, placements and inputs. Thus routes of length $O(\ell)$ cost $O(\ell)$ per round, without a congestion bound. Colors are reused and do not replace unique routing identities.
--
--   This is the preprocessing and simulation interface needed to avoid paying a fresh coloring overhead at every stage.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs → SimpleGraph (Fin N), with arbitrary supplied bounds n and degree; reason: every finite simple graph can be relabelled in this way; the carrier index is never processor input
--   - encoding: deterministic synchronous LOCAL algorithms → tape-independent published LocalAlg programs with source-only local inputs and endpoint-consistent outputs; reason: rules and types precede graph inputs; multiset broadcast supports addressed dictionaries without bandwidth restrictions
--   - encoding: asymptotic base-two logarithmic bounds → uniform positive constants, natural ceiling budgets and logarithms padded to at least one; reason: only bounded-parameter conventions change; empty and degree-zero or degree-one graphs remain included
--   - encoding: unique O(log n)-bit identifiers → every injection below max(2,n)^(b+1), for each fixed natural b; reason: the protocol and constants may depend on the fixed ID convention, and never on a graph, its identifiers or epsilon
--   - generalization: virtual graphs arising in the bipartite matching section → locally paired active edges of an arbitrary finite simple graph; reason: the block, cut expectation and cut derandomization statements use degree at most two and local creator counts, not the parity of cycles; bipartite stages are included
--   - encoding: Delta^O(ell) colors and edge color plus endpoint bit → max(2,Delta)^(a ell) edge colors and twice that many copy colors, with a uniform natural a; reason: constant factors and small degrees are absorbed in the source exponential palette
--   - generalization: auxiliary graphs on virtual copies with O(ell) routes → every finite hosted auxiliary graph with supplied walks of length at most r, and a separate route-free line-power simulator; reason: unbounded messages make congestion irrelevant; taking r=O(ell) and the source copy placement recovers the source claim
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Lemma 3.3, printed p.9, PDF p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing

namespace FasterDistributedMatching.ApproximateMatching

/- Lemma 3.3, printed p.9 / PDF p.11 and Appendix A printed p.22 / PDF p.24.
The coloring is computed once and works for every later local pairing and copy-edge choice.
The final conjunct gives operational simulation for all supplied bounded-length routes. -/
theorem lemma_3_3 :
    RoutedSimulation ∧ LineSimulation ∧
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
