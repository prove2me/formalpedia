-- Prove2me | Theorems.Thm_EuclidKSteiner_observation_5_1
-- name    : EuclidKSteiner.observation_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:38.298201+00:00
-- url     : https://prove2.me/theorems/f857485b-2667-46ac-9296-0790b5a77e92
-- title:
--   Observation 5.1 — $\mathrm{red}_\chi(A)+\mathrm{blue}_\chi(B)\le\mathrm{len}(\mathrm{Merge}_M(A\cup B))$, with equality for separating $\chi$
-- statement:
--   Let $M$ be a tree on $P$ with nonnegative edge weights. For every red–blue coloring $\chi$ of the edges of $\mathrm{Merge}_M$ and all disjoint $A,B\subseteq P$,
--   $$\mathrm{red}_\chi(A)+\mathrm{blue}_\chi(B)\le\mathrm{len}\bigl(\mathrm{Merge}_M(A\cup B)\bigr),$$
--   and equality holds if $\chi$ separates $A$ and $B$.
--
--   With Lemma 3.10 this splits $\Phi(A\cup B)$ into a part depending on $A$ and a part depending on $B$, which is what makes the selection rule of Theorem 3.8 correct.
--
--   Differences from the source:
--   - encoding: the merge tree Merge_M recording Kruskal's algorithm and its edges → clusters (singletons and the components of M≤t at edge weights t), each edge named by its child cluster, of length h(parent) − h(child); Merge_M(X) the clusters C ≠ P meeting X; reason: the page identifies each vertex with its cluster
--   - encoding: red–blue edge colorings of Merge_M → maps from clusters (edges named by their child cluster) to Bool, false = red, true = blue; reason: the merge-tree encoding by clusters
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Observation 5.1, (5.1), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_EuclidKSteiner_MergeTree

namespace EuclidKSteiner

/-- **Observation 5.1.** Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean
k-Steiner Tree*, STOC 2027 submission (manuscript sha256 75361687…), Observation 5.1, (5.1), p.20
(PDF p.22): "For every red–blue edge coloring χ of Merge_M and disjoint leaf sets A, B,
red_χ(A) + blue_χ(B) ≤ len(Merge_M(A ∪ B)). If χ separates A and B, then equality holds."

For every tree `M` on `P` with nonnegative weights, every red–blue coloring `χ` of the edges of
`Merge_M` and all disjoint `A, B ⊆ P`:
`red_χ(A) + blue_χ(B) ≤ len(Merge_M(A ∪ B))`, with equality when `χ` separates `A` and `B`. -/
theorem observation_5_1 {V : Type*} [DecidableEq V] (T : TermTree V) (χ : Finset V → Bool)
    (A B : Finset V) (hA : A ⊆ T.P) (hB : B ⊆ T.P) (hAB : Disjoint A B) :
    T.redLen χ A + T.blueLen χ B ≤ T.lenMerge (A ∪ B) ∧
      (T.Separates χ A B → T.redLen χ A + T.blueLen χ B = T.lenMerge (A ∪ B)) := by sorry

end EuclidKSteiner
