-- Prove2me | Theorems.Thm_BrinSquier_metabelian_or_freeAbelianBasis_infinite
-- name    : BrinSquier.metabelian_or_freeAbelianBasis_infinite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T09:29:13.630746+00:00
-- url     : https://prove2.me/theorems/c95db421-65f7-4961-9f49-4c951d781c88
-- title:
--   (3.3) A subgroup of PLF(ℝ) is metabelian or contains a free abelian subgroup of infinite rank
-- statement:
--   Brin-Squier's Corollary (3.3) with its **full** conclusion. For any subgroup $G$ of $\mathrm{PLF}(\mathbb{R})$ — no condition on the slopes at the ends — either the derived subgroup $\lbrack G, G \rbrack$ is abelian, so $G$ is metabelian, or $G$ contains a free abelian subgroup of **infinite rank**.
--
--   The proof is the source's one line, *apply (3.2) to the commutator subgroup*, with the infinite-rank form of (3.2). The step that makes it work is that the derived subgroup satisfies the slope-one hypothesis even though $G$ need not: a commutator has slope one at both ends by (2.14a), and the slope-one maps form a subgroup, so every element of $\lbrack G, G \rbrack$ qualifies.
--
--   **Relation to the rank-two milestone.** The companion corollary concludes only a copy of $\mathbb{Z}^2$ in the second horn. This is the source's statement, and it is the result Brin and Squier describe as "the somewhat stronger" one from which their Theorem (3.1) follows: a free group of rank greater than one is neither metabelian nor contains a free abelian group of infinite rank.
--
--   **Formalization note.** "Metabelian" is rendered as the elements of $\lbrack G, G \rbrack$ commuting pairwise, Mathlib having no `Metabelian` predicate. Freeness is stated in **two** parts, matching what "freely generates a free abelian group" asserts: the generators commute pairwise, and the only relation among them is the trivial one. The relation condition avoids `Finsupp.prod`, which needs a commutative monoid and the group of order isomorphisms is not one; instead the source's own phrasing is used, which writes an element of the generated group as $g_1^{n_1} g_2^{n_2} \cdots g_k^{n_k}$ with the $g_i$ **distinct**, so the condition is an ordered product over a duplicate-free list. Given the commutativity conjunct that is equivalent to the usual basis condition, every word in the generators reducing to that form.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 494, Corollary (3.3): "Let G be a subgroup of PLF(R). Then either G is metabelian or G contains a free abelian subgroup of infinite rank. Proof. Apply (3.2) to the commutator subgroup G' of G." This is the full statement, unweakened. PROVENANCE NOTE: this supersedes an earlier statement of the same result which omitted the pairwise-commutativity conjunct and so did not in fact assert free abelianness; a blind read-back audit caught the omission.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem metabelian_or_freeAbelianBasis_infinite (G : Subgroup (ℝ ≃o ℝ)) (hG : ∀ f ∈ G, IsPLF f) :
    (∀ u ∈ ⁅G, G⁆, ∀ v ∈ ⁅G, G⁆, u * v = v * u) ∨
      ∃ x : ℤ → ℝ ≃o ℝ, (∀ m, x m ∈ G) ∧ (∀ p q : ℤ, x p * x q = x q * x p) ∧
        ∀ (l : List ℤ), l.Nodup → ∀ n : ℤ → ℤ,
          (l.map (fun m => x m ^ n m)).prod = 1 → ∀ m ∈ l, n m = 0 := by
  sorry

end BrinSquier
