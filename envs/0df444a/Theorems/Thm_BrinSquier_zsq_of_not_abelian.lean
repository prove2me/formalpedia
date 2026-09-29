-- Prove2me | Theorems.Thm_BrinSquier_zsq_of_not_abelian
-- name    : BrinSquier.zsq_of_not_abelian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:18:12.681687+00:00
-- url     : https://prove2.me/theorems/597f5ff6-741a-4cbd-8c76-9b98536c1a52
-- title:
--   A non-abelian subgroup of PLF′(ℝ) contains a copy of ℤ²
-- statement:
--   Let $G$ be a group of piecewise-linear homeomorphisms of $\mathbb{R}$ with finitely many breakpoints, each of which is a translation near $-\infty$ and near $+\infty$ — that is, a subgroup of $\mathrm{PLF}'(\mathbb{R})$. If $G$ is **not abelian**, then $G$ contains a copy of $\mathbb{Z}^2$: there are $u, v \in G$ that commute and for which
--
--   $$(m,n) \longmapsto u^{m} v^{n}, \qquad \mathbb{Z}^2 \to G,$$
--
--   is injective.
--
--   Commutativity is what makes that map a homomorphism, and injectivity then makes its image a subgroup of $G$ isomorphic to $\mathbb{Z}\times\mathbb{Z}$. The statement itself produces no subgroup object and no isomorphism. Nothing is claimed about $u$ and $v$ beyond the two conjuncts: they need not be commutators, need not have disjoint or bounded support, and are unrelated to whichever pair witnesses non-commutativity.
--
--   **Relation to the source.** Brin–Squier's Theorem (3.2) concludes more: such a $G$ contains a free abelian subgroup of **infinite rank**. Only rank two is stated here: rank two is all the goal consumes, and the infinite-rank conclusion needs the general form of their Lemma (1.2), which this mission does not formalize. Monod makes the same cut when generalizing the argument to piecewise-projective homeomorphisms: Theorem 14 there also stops at rank two. (That version is stated for two-generated subgroups, with a metabelian rather than abelian first horn.)
--
--   **The slope-one hypothesis is load-bearing.** It cannot be weakened to plain piecewise linearity. Take $M : y \mapsto 2y$ and $T : y \mapsto y+1$, both piecewise linear. They satisfy $M T M^{-1} = T^{2}$, the defining relation of the Baumslag–Solitar group $BS(1,2)$, and together they generate $\{\, y \mapsto 2^{n} y + b \;:\; n \in \mathbb{Z},\ b \in \mathbb{Z}[1/2] \,\}$. That group is non-abelian and every element of it is piecewise linear, yet it contains no $\mathbb{Z}^2$ at all: every abelian subgroup of it has rank at most one ([`BrinSquier.bs12_no_zsq`](https://prove2.me/theorems/772dff2f-9713-49b3-acce-f78b593726d0)).
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 494, Theorem (3.2) (proof on p. 495), with the conclusion weakened from free abelian of infinite rank to rank two.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem zsq_of_not_abelian (G : Subgroup (ℝ ≃o ℝ))
    (hG : ∀ f ∈ G, IsPLFSlopeOne f) (hne : ¬ ∀ f ∈ G, ∀ g ∈ G, f * g = g * f) :
    ∃ u ∈ G, ∃ v ∈ G, u * v = v * u ∧
      Function.Injective (fun p : ℤ × ℤ => u ^ p.1 * v ^ p.2) := by
  sorry

end BrinSquier
