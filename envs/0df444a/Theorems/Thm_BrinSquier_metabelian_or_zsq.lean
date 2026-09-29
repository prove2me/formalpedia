-- Prove2me | Theorems.Thm_BrinSquier_metabelian_or_zsq
-- name    : BrinSquier.metabelian_or_zsq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T08:17:12.257385+00:00
-- url     : https://prove2.me/theorems/2d12435b-5410-49df-a187-1cb69c2dee6e
-- title:
--   (3.3) A subgroup of PLF(ℝ) is metabelian or contains a copy of ℤ²
-- statement:
--   Let $G$ be a group of piecewise-linear homeomorphisms of $\mathbb{R}$, each with finitely many breakpoints — that is, a subgroup of $\mathrm{PLF}(\mathbb{R})$. Then **either** the derived subgroup $\lbrack G, G \rbrack$ is abelian, so that $G$ is metabelian, **or** $G$ contains a copy of $\mathbb{Z}^2$: commuting $u, v \in G$ for which
--
--   $$(m,n) \longmapsto u^{m} v^{n}, \qquad \mathbb{Z}^2 \to G,$$
--
--   is injective.
--
--   Note the hypothesis is *plain* $\mathrm{PLF}(\mathbb{R})$, with no condition on the slopes at the two ends. That is the difference from the main dichotomy (3.2), which requires slope one at each end: here the slope condition is *derived* rather than assumed, because a commutator has slope one at both ends whatever its factors do.
--
--   **Relation to the source.** Brin–Squier's Corollary (3.3) concludes more in the second horn: a free abelian subgroup of **infinite rank**. Only rank two is claimed here, matching this mission's rank-two form of (3.2); the infinite-rank conclusion needs the general form of their Lemma (1.2), which this mission does not formalize. The first horn, metabelian, is unweakened.
--
--   **Formalization note.** "Metabelian" is rendered as the elements of $\lbrack G, G \rbrack$ commuting pairwise, rather than through a `Metabelian` predicate, which Mathlib does not have. A copy of $\mathbb{Z}^2$ is an injectivity statement about $(m,n) \mapsto u^m v^n$, not a subgroup isomorphism, and no subgroup object is produced.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 494: "(3.3) Corollary. Let G be a subgroup of PLF(R). Then either G is metabelian or G contains a free abelian subgroup of infinite rank. Proof. Apply (3.2) to the commutator subgroup G' of G." PROVENANCE: the second horn is weakened here from free abelian of infinite rank to a copy of Z^2, matching this mission's rank-two form of Theorem (3.2), p. 494. The first horn and the hypothesis are as in the source.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem metabelian_or_zsq (G : Subgroup (ℝ ≃o ℝ)) (hG : ∀ f ∈ G, IsPLF f) :
    (∀ u ∈ ⁅G, G⁆, ∀ v ∈ ⁅G, G⁆, u * v = v * u) ∨
      ∃ u ∈ G, ∃ v ∈ G, u * v = v * u ∧
        Function.Injective (fun p : ℤ × ℤ => u ^ p.1 * v ^ p.2) := by
  sorry

end BrinSquier
