-- Prove2me | Theorems.Thm_BrinSquier_freeAbelian_infinite_of_not_abelian
-- name    : BrinSquier.freeAbelian_infinite_of_not_abelian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T08:43:45.357993+00:00
-- url     : https://prove2.me/theorems/7abf07fb-23e8-4219-b759-b640d471b24d
-- title:
--   (3.2) A non-abelian subgroup of PLF'(ℝ) contains a free abelian subgroup of infinite rank
-- statement:
--   Brin-Squier's Theorem (3.2) with its **full** conclusion. Let $G$ be a group of piecewise-linear homeomorphisms of $\mathbb{R}$ with finitely many breakpoints, each a translation near $-\infty$ and near $+\infty$ — that is, $G \le \mathrm{PLF}'(\mathbb{R})$. If $G$ is **not abelian**, then $G$ contains a free abelian subgroup of **infinite rank**: an $\mathbb{Z}$-indexed family in $G$ that freely generates a free abelian group.
--
--   **Relation to the rank-two milestone.** The separate milestone concludes only a copy of $\mathbb{Z}^{2}$, which is all the mission's goal consumes. This is the source's actual conclusion. The proof is the same page-495 argument, but where the rank-two form needs a single conjugate $z w z^{-1}$, this one needs the whole family $z^{m} w z^{-m}$ for $m \in \mathbb{Z}$: their moved sets meet the chosen component in the pairwise disjoint intervals $(z^{m}(c), z^{m}(d))$, the minimality of the component count forces them to commute pairwise, and the general form of Lemma (1.2) then makes them a free basis.
--
--   **Formalization note.** Freeness is rendered without a `Finsupp` product, because the group of order isomorphisms is not commutative and `Finsupp.prod` requires a commutative monoid. Instead the source's own phrasing is used: it writes an element of the generated group as $g_1^{n_1} g_2^{n_2} \cdots g_k^{n_k}$ with the $g_i$ **distinct**, so the condition is stated for an ordered product over a duplicate-free list. Since the generators commute the order is immaterial, and no commutativity hypothesis is needed to state it. The family is indexed by $\mathbb{Z}$, so the rank is countably infinite; the freeness condition also forces the $x_m$ to be distinct, since otherwise two exponents $1$ and $-1$ would give a trivial product. No subgroup object is produced.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 494, Theorem (3.2): "Let G be a subgroup of PLF'(R). Then either G is abelian or G contains a free abelian subgroup of infinite rank." Proof on p. 495. This is the full statement, unweakened; the mission's other (3.2) milestone weakens the conclusion to rank two.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem freeAbelian_infinite_of_not_abelian (G : Subgroup (ℝ ≃o ℝ))
    (hG : ∀ f ∈ G, IsPLFSlopeOne f) (hne : ¬ ∀ f ∈ G, ∀ g ∈ G, f * g = g * f) :
    ∃ x : ℤ → ℝ ≃o ℝ, (∀ m, x m ∈ G) ∧
      ∀ (l : List ℤ), l.Nodup → ∀ n : ℤ → ℤ,
        (l.map (fun m => x m ^ n m)).prod = 1 → ∀ m ∈ l, n m = 0 := by
  sorry

end BrinSquier
