-- Prove2me | Theorems.Thm_DirectedTreeCovers_Strong_lemma_5_2
-- name    : DirectedTreeCovers.Strong.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:29:28.385848+00:00
-- url     : https://prove2.me/theorems/30771bb6-b081-47e5-af48-e94ff4972704
-- title:
--   Lemma 5.2 — expected expanded bunch size
-- statement:
--   There is an absolute constant $C>0$ such that, for every finite strongly connected directed graph $G$ with nonnegative real weights, every integer $k\ge1$ and every vertex $v$, the expanded bunch produced by Algorithm 3 under the unforced independent hierarchy law satisfies
--
--   $$\mathbb E[|EB(v)|]\le Ck\,n^{1/k},\qquad n=|V|.$$
--
--   The bunch is the union of centers whose actual expanded clusters contain $v$. The expectation uses one common hierarchy law, allowing empty top levels. Since actual tree-pair overlap is at most this bunch size, this is the overlap estimate needed for Theorem 1.2.
--
--   Differences from the source:
--   - generalization: finite directed graphs → finite directed multigraphs, allowing parallel edges and loops; reason: simple directed graphs embed by their edge identities; finite nonnegative shortest walks still exist
--   - reading: searches rooted in a possibly empty expanded cluster → missing-root searches return empty slots, omitted from the pair collection; reason: zero radii can exclude the root; no path is lost by omitting a search with no reachable vertex
--   - encoding: incoming and outgoing shortest-path searches with fixed ties → tight parent edges with decreasing minimum shortest-walk hop count and a fixed finite-set selector; reason: this selects genuine shortest-path trees and prevents zero-weight cycles without restricting weights
--   - encoding: expectation under independent retention with probability n^(-1/k) → a finite Bernoulli product law and a sum over its atom masses; reason: the rate is unchanged on n>=1,k>=1 and the law has mass one; finite sums have no integrability default
--   - encoding: O(k*n^(1/k)) → a single existential positive real C preceding all graph, weight, k and vertex quantifiers; reason: this is the absolute uniform interpretation of the source bound; the exponent uses real division
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/840.pdf, Lemma 5.2, printed p.18 (PDF p.19); §§5.1–5.3, printed pp.16–18 (PDF pp.17–19)

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Construction

namespace DirectedTreeCovers.Strong

/-- Lemma 5.2, Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840
(October 2026), printed p.18 / PDF p.19. One absolute constant is chosen before
all graph, weight, k and vertex instances. The finite expectation is taken under
the unforced independent Bernoulli hierarchy, not an arbitrary law or certificate. -/
theorem lemma_5_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : EulerSparsify.DiGraph V E),
        Nonnegative G → StronglyConnected G → ∀ k : ℕ, 1 ≤ k → ∀ v : V,
          expectedBunch G k v ≤ C * (k : ℝ) * (Fintype.card V : ℝ) ^ (1 / (k : ℝ)) := by sorry

end DirectedTreeCovers.Strong
