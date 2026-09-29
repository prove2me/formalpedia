-- Prove2me | Theorems.Thm_AKSSorting_Core_splitV_spec
-- name    : AKSSorting.Core.splitV_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T10:08:40.8157+00:00
-- url     : https://prove2.me/theorems/95bf217f-7f01-4b56-b480-ea781c723b37
-- title:
--   Lemma 1 — the splitting V(C, k) consists of chains with properties (1.1)–(1.5)
-- statement:
--   Let $C$ be a chain on level $i$ with $N(C)\ge 2$, let $0\le j<i$, and let $V(C,k)$, $0\le k\le i$, be the splitting of Lemma 1 (one register of every leaf set of $C$ moved up to a level between $j$ and $i-1$, two of them to each node of level $j$). Then $V(C,k)$ is a chain for every $0\le k\le i$, and:
--
--   1. (1.1) $l(V(C,k))=k$;
--   2. (1.2) $(\cup V(C,k))\cap(\cup V(C,k'))=\emptyset$ for $k\ne k'$;
--   3. (1.3) $N(V(C,k))=1$ for $j<k<i$, $N(V(C,j))=2$, and $N(V(C,k))=0$ for $0\le k<j$;
--   4. (1.4) for every node $t'$ with $j\le l(t')\le i$,
--   $$ V(C,l(t'))(t')\subseteq\bigcup_{l(t)=i,\ t\prec t'}C(t); $$
--   5. (1.5) for every $t$ of level $i$,
--   $$ \Bigl|\,C(t)\cap\bigcup_{0\le k<i}\bigl(\cup V(C,k)\bigr)\Bigr|=1 . $$
--
--   The splitting moves exactly one register out of each leaf set, and only to ancestors of that leaf.
--
--   **Formalization Note** (1.1) is carried by the type: $V(C,k)$ is a function on `Fin (2^k)`. In (1.4) the paper's free index $k$ is $l(t')$. $N(\cdot)$ is evaluated at node $0$; together with the chain property this is the paper's "for some (all) $x$".
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), pp. 3-4, Lemma 1

import Mathlib
import Definitions.Def_AKSSorting_Core_IsChain
import Definitions.Def_AKSSorting_Core_splitV

namespace AKSSorting.Core

/-- Lemma 1 (Ajtai–Komlós–Szemerédi 1983, pp. 3–4). Let `C` be a chain on level `i`,
`0 ≤ j < i`, and `N(C) ≥ 2`. Then `V(C, k)` is a chain for all `0 ≤ k ≤ i` ((1.1),
`l(V(C, k)) = k`, is carried by the type `Fin (2 ^ k) → Finset R`), and
* (1.2) `∪V(C, k)` and `∪V(C, k')` are disjoint for `k ≠ k'`;
* (1.3) `N(V(C, k)) = 1` for `j < k < i`, `N(V(C, j)) = 2`, `N(V(C, k)) = 0` for `k < j`;
* (1.4) for every node `t'` with `j ≤ l(t') ≤ i`,
  `V(C, l(t'))(t') ⊆ ⋃_{l(t) = i, t ≺ t'} C(t)`;
* (1.5) for every `t ∈ Dom(C)`, `|C(t) ∩ ⋃_{0 ≤ k < i} ∪V(C, k)| = 1`. -/
theorem splitV_spec {R : Type} [LinearOrder R] {i j : ℕ} (C : Fin (2 ^ i) → Finset R)
    (hC : IsChain C) (hj : j < i) (hN : 2 ≤ chainN C) :
    (∀ k ≤ i, IsChain (splitV C j k)) ∧
    (∀ k ≤ i, ∀ k' ≤ i, k ≠ k' →
      Disjoint (chainUnion (splitV C j k)) (chainUnion (splitV C j k'))) ∧
    ((∀ k, j < k → k < i → chainN (splitV C j k) = 1) ∧
      chainN (splitV C j j) = 2 ∧
      (∀ k, k < j → chainN (splitV C j k) = 0)) ∧
    (∀ k, j ≤ k → k ≤ i → ∀ t' : Fin (2 ^ k), splitV C j k t' ⊆ subtreeUnion C k t') ∧
    (∀ t : Fin (2 ^ i),
      (C t ∩ (Finset.range i).biUnion fun k => chainUnion (splitV C j k)).card = 1) := by sorry

end AKSSorting.Core
