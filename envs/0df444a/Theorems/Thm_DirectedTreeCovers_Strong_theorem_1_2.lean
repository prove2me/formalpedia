-- Prove2me | Theorems.Thm_DirectedTreeCovers_Strong_theorem_1_2
-- name    : DirectedTreeCovers.Strong.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:16.005588+00:00
-- url     : https://prove2.me/theorems/dfb2b805-be3e-48f2-a6a9-a34615884221
-- title:
--   Theorem 1.2 — strong stretch with low expected overlap
-- statement:
--   There is an absolute constant $C>0$ such that every finite directed graph $G=(V,E,\omega)$ with arbitrary nonnegative real edge weights and every integer $k\ge1$ admit a finite probability law on finite collections $\mathcal T$ of genuine weighted directed tree-pairs. On every outcome of positive mass, all ordered pairs are simultaneously covered:
--
--   $$\forall u,v\in V,\quad\exists T\in\mathcal T:\ d_T(u,v)\le k\,d_G(u,v)+(k-1)d_G(v,u).$$
--
--   Under that same law, for every vertex $v$,
--
--   $$\mathbb E\big[\#\{T\in\mathcal T:v\in V(T_{\rm in})\cup V(T_{\rm out})\}\big]\le Ck\,n^{1/k},\qquad n=|V|.$$
--
--   The exact additive form on finite roundtrip pairs is $d_T(u,v)\le d_G(u,v)+(k-1)r_G(u,v)$. No connectivity, positivity, integer-weight, distinct-endpoint or large-$k$ assumption is imposed. At $k=1$, reachable pairs receive exact one-way distances even across strongly connected components. Empty inputs have an empty cover. This is the headline structural result; preprocessing times, spanners, oracles and routing are separate results.
--
--   Differences from the source:
--   - generalization: finite directed graphs → finite directed multigraphs, allowing parallel edges and loops; reason: simple directed graphs embed by their edge identities; finite nonnegative shortest walks still exist
--   - reading: every ordered pair, alongside the strongly connected component convention → all ordered pairs under the second extended-distance formula, including exact one-way distances at k=1; reason: this is the stronger reading; all-root shortest-path pairs cover cross-component one-way paths at k=1, while k>=2 has infinite bound across components
--   - encoding: extended shortest-walk distances and the strong-stretch inequality → ENNReal distances and k*d(u,v)+(k-1)*d(v,u), with 0*infinity=0; reason: the source displays this equivalent form in Section 2; k>=1 makes natural subtraction exact
--   - encoding: a random finite collection of tree-pairs → Fin m atom masses in NNReal summing to one and a list of pairs per atom, with validity and simultaneous stretch on positive-mass atoms; reason: the source uses finitely many coins; repetitions are counted separately and may be removed without increasing overlap
--   - encoding: weighted incoming and outgoing shortest-path trees with a common root → bare rooted data plus original parent-edge maps, explicit parent termination, and shortest root paths in a stored induced region; reason: this represents actual directed trees, retains distinct in/out supports, and excludes zero-weight cycles without a positivity assumption
--   - encoding: O(k*n^(1/k)) → a single existential positive real C preceding all graph, weight, k and vertex quantifiers; reason: this is the absolute uniform interpretation of the source bound; the exponent uses real division
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/840.pdf, Theorem 1.2, printed p.3 (PDF p.4); tree-pair and strong-stretch definitions §2, printed pp.6–7 (PDF pp.7–8)

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Trees

namespace DirectedTreeCovers.Strong

/-- Theorem 1.2, Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840
(October 2026), printed p.3 / PDF p.4; strong stretch in §2, printed p.7 / PDF p.8.
One finite probability law gives simultaneous all-pairs stretch and all per-vertex
expected overlap bounds. It has total mass one. No connectivity or positivity
restriction is imposed. The stronger all-pairs reading includes exact one-way paths
at k = 1. Parallel edges and loops are also permitted. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : EulerSparsify.DiGraph V E),
        Nonnegative G → ∀ k : ℕ, 1 ≤ k →
          ∃ (m : ℕ) (p : Fin m → NNReal) (covers : Fin m → List (TreePair V E)),
            (∑ o : Fin m, p o) = 1 ∧
            (∀ o, p o ≠ 0 → StrongCover G k (covers o)) ∧
            ∀ v : V, (∑ o : Fin m, (p o : ℝ) * (overlap (covers o) v : ℝ)) ≤
              C * (k : ℝ) * (Fintype.card V : ℝ) ^ (1 / (k : ℝ)) := by sorry

end DirectedTreeCovers.Strong
