-- Prove2me | Theorems.Thm_BrinSquier_freeAbelianBasis_infinite_of_not_abelian
-- name    : BrinSquier.freeAbelianBasis_infinite_of_not_abelian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T09:29:03.207193+00:00
-- url     : https://prove2.me/theorems/f9d45795-b2ee-43de-b128-9f1501cf7eea
-- title:
--   (3.2) A non-abelian subgroup of PLF'(ℝ) contains a free abelian subgroup of infinite rank
-- statement:
--   Brin-Squier's Theorem (3.2) with its **full** conclusion. Let $G$ be a group of piecewise-linear homeomorphisms of $\mathbb{R}$ with finitely many breakpoints, each a translation near $-\infty$ and near $+\infty$ — that is, $G \le \mathrm{PLF}'(\mathbb{R})$. If $G$ is **not abelian**, then $G$ contains a free abelian subgroup of **infinite rank**: a $\mathbb{Z}$-indexed family in $G$ that commutes pairwise and freely generates a free abelian group.
--
--   **Relation to the rank-two milestone.** The separate milestone concludes only a copy of $\mathbb{Z}^{2}$, which is all the mission's goal consumes. This is the source's actual conclusion. The proof is the same page-495 argument, but where the rank-two form needs a single conjugate $z w z^{-1}$, this one needs the whole family $z^{m} w z^{-m}$ for $m \in \mathbb{Z}$: their moved sets meet the chosen component in the pairwise disjoint intervals $(z^{m}(c), z^{m}(d))$, the minimality of the component count forces them to commute pairwise, and the general form of Lemma (1.2) then makes them a free basis.
--
--   **Formalization note.** Freeness is stated in **two** parts, matching what "freely generates a free abelian group" asserts: the generators commute pairwise, and the only relation among them is the trivial one. The relation condition avoids `Finsupp.prod`, which needs a commutative monoid and the group of order isomorphisms is not one; instead the source's own phrasing is used, which writes an element of the generated group as $g_1^{n_1} g_2^{n_2} \cdots g_k^{n_k}$ with the $g_i$ **distinct**, so the condition is an ordered product over a duplicate-free list. Given the commutativity conjunct that is equivalent to the usual basis condition, every word in the generators reducing to that form. The family is indexed by $\mathbb{Z}$, so the rank is countably infinite; the relation condition also forces the $x_m$ to be distinct, since otherwise two exponents $1$ and $-1$ would give a trivial product. No subgroup object is produced.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 494, Theorem (3.2): "Let G be a subgroup of PLF'(R). Then either G is abelian or G contains a free abelian subgroup of infinite rank." Proof on p. 495. This is the full statement, unweakened; the mission's other (3.2) milestone weakens the conclusion to rank two. PROVENANCE NOTE: this supersedes an earlier statement of the same result which omitted the pairwise-commutativity conjunct and so did not in fact assert free abelianness; a blind read-back audit caught the omission.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem freeAbelianBasis_infinite_of_not_abelian (G : Subgroup (ℝ ≃o ℝ))
    (hG : ∀ f ∈ G, IsPLFSlopeOne f) (hne : ¬ ∀ f ∈ G, ∀ g ∈ G, f * g = g * f) :
    ∃ x : ℤ → ℝ ≃o ℝ, (∀ m, x m ∈ G) ∧ (∀ p q : ℤ, x p * x q = x q * x p) ∧
      ∀ (l : List ℤ), l.Nodup → ∀ n : ℤ → ℤ,
        (l.map (fun m => x m ^ n m)).prod = 1 → ∀ m ∈ l, n m = 0 := by
  sorry

end BrinSquier
