-- Prove2me | Theorems.Thm_EuclidKSteiner_lemma_3_10
-- name    : EuclidKSteiner.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:47.454635+00:00
-- url     : https://prove2.me/theorems/70e6302f-8ef2-43d2-bef9-818d96e14b89
-- title:
--   Lemma 3.10 — path-union formula $\Phi(X)=\mathrm{len}(\mathrm{Merge}_M(X))-h(\rho)$
-- statement:
--   Let $M$ be a tree on $P$ with nonnegative edge weights, $\mathrm{Merge}_M$ its merge tree with root $\rho$ and heights $h$. For every nonempty $X\subseteq P$,
--   $$\Phi(X)=\mathrm{len}\bigl(\mathrm{Merge}_M(X)\bigr)-h(\rho).$$
--
--   The formula makes $\Phi(A\cup B)$ a length of a union of root-to-leaf paths, which the separating colorings of §5 split into a contribution from $A$ and one from $B$.
--
--   Differences from the source:
--   - generalization: M the fixed minimum spanning tree of G[P] (§3) → M any tree on P with nonnegative edge weights (TermTree); reason: the page says "The construction also applies when M is any tree with nonnegative edge weights" and §5 applies (3.6) to the arbitrary tree of Theorem 3.8; the fixed MST of G[P] is such a tree
--   - encoding: the merge tree Merge_M recording Kruskal's algorithm → clusters: singletons and the components of M≤t for t an edge weight of M; heights by the largest inner edge weight; parent the smallest strictly larger cluster; Merge_M(X) the clusters C ≠ P meeting X; reason: the page identifies each vertex with its cluster and the height with the merge weight
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 3.10, (3.6), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_EuclidKSteiner_MergeTree

namespace EuclidKSteiner

/-- **Lemma 3.10 (Path-union formula).** Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized
Tractability of Euclidean k-Steiner Tree*, STOC 2027 submission (manuscript sha256 75361687…),
Lemma 3.10, (3.6), p.13 (PDF p.15): "For every nonempty X ⊆ P, Φ(X) = len(Merge_M(X)) − h(ρ)."

For every tree `M` on `P` with nonnegative edge weights and every nonempty `X ⊆ P`,
`Φ(X) = len(Merge_M(X)) − h(ρ)`.

**Formalization Note** `M` is any tree on `P` with nonnegative weights ("The construction also
applies when M is any tree with nonnegative edge weights", p.13). The merge tree is encoded by its
clusters (see `TermTree.clusters`). -/
theorem lemma_3_10 {V : Type*} [DecidableEq V] (T : TermTree V) (X : Finset V)
    (hX : X.Nonempty) (hXP : X ⊆ T.P) :
    T.Phi X = T.lenMerge X - T.rootHeight := by sorry

end EuclidKSteiner
