-- Prove2me | Theorems.Thm_BrinSquier_freeAbelian_of_disjoint_supp
-- name    : BrinSquier.freeAbelian_of_disjoint_supp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T08:43:20.912753+00:00
-- url     : https://prove2.me/theorems/5fcb5166-1615-4eda-98bb-67c5e3ccd796
-- title:
--   (1.2) A family of infinite-order maps with pairwise disjoint supports is free abelian
-- statement:
--   Let $(x_i)_{i \in \iota}$ be a family of order isomorphisms of $\mathbb{R}$ such that
--
--   - no nonzero power of any $x_i$ is the identity, and
--   - for $i \neq j$, every point is fixed by $x_i$ or by $x_j$ — the moved sets are pairwise disjoint.
--
--   Then the family freely generates a free abelian group: for any duplicate-free list of indices and any exponents, if the product $\prod x_i^{n_i}$ over that list is the identity, every exponent involved is zero.
--
--   The mechanism is that disjointness lets one factor be isolated. Restricted to $\operatorname{supp} x_i$, every other factor acts trivially, so the whole product acts there as $x_i^{n_i}$; and since $x_i^{n_i}$ moves nothing outside $\operatorname{supp} x_i$ either, the product being the identity forces $x_i^{n_i} = 1$, hence $n_i = 0$.
--
--   **Role.** This is the engine behind free abelian subgroups of **infinite** rank. The rank-two case is the separate milestone about two disjointly supported elements; the general family is what upgrades the main dichotomy (3.2) from a copy of $\mathbb{Z}^2$ to free abelian of infinite rank, which is the conclusion Brin and Squier actually prove.
--
--   **Formalization note.** Freeness is rendered without a `Finsupp` product, because the group of order isomorphisms is not commutative and `Finsupp.prod` requires a commutative monoid. Instead the source's own phrasing is used: it writes an element of the generated group as $g_1^{n_1} g_2^{n_2} \cdots g_k^{n_k}$ with the $g_i$ **distinct**, so the condition is stated for an ordered product over a duplicate-free list. Since the generators commute the order is immaterial, and no commutativity hypothesis is needed to state it. The hypotheses are stated for $\mathbb{R} \simeq_o \mathbb{R}$; the source states them for the full symmetric group of an arbitrary set, and nothing in the argument uses the order or the topology.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 488, Lemma (1.2): "Let A be a set and let X be a subset of S_A. Suppose (a) each f in X has infinite order, and (b) if f, g in X satisfy f != g, then supp f and supp g are disjoint. Then X freely generates a free abelian group of permutations of A." PROVENANCE: specialized here from permutations of an arbitrary set to order isomorphisms of R, and 'freely generates a free abelian group' is rendered as the ordered-product condition over a duplicate-free list of indices, matching the paper's own proof, which writes an element as g_1^{n_1}...g_k^{n_k} with the g_i distinct.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem freeAbelian_of_disjoint_supp {ι : Type*} (x : ι → ℝ ≃o ℝ)
    (hinf : ∀ i, ∀ k : ℤ, k ≠ 0 → x i ^ k ≠ 1)
    (hdisj : ∀ i j, i ≠ j → ∀ a : ℝ, x i a = a ∨ x j a = a)
    (l : List ι) (hl : l.Nodup) (n : ι → ℤ)
    (hprod : (l.map (fun i => x i ^ n i)).prod = 1) :
    ∀ i ∈ l, n i = 0 := by
  sorry

end BrinSquier
