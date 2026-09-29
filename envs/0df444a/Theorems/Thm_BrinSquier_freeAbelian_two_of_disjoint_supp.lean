-- Prove2me | Theorems.Thm_BrinSquier_freeAbelian_two_of_disjoint_supp
-- name    : BrinSquier.freeAbelian_two_of_disjoint_supp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:07:41.23173+00:00
-- url     : https://prove2.me/theorems/c3adbe81-1fd5-4c1a-8759-437a2a283191
-- title:
--   Two nontrivial homeomorphisms with disjoint supports are independent
-- statement:
--   Let $u,v$ be orientation-preserving homeomorphisms of $\mathbb{R}$, each of infinite order, whose supports are disjoint. Then
--
--   $$(m,n) \longmapsto u^{m} v^{n}, \qquad \mathbb{Z}^2 \to \mathrm{Homeo}_+(\mathbb{R}),$$
--
--   is injective: no two distinct integer pairs give the same element.
--
--   Together with the previous milestone — disjoint supports force $u$ and $v$ to commute — this says exactly that $u$ and $v$ generate a **free abelian group of rank two**. Stated alone, the injectivity does not say that: in a free group of rank two the same map is injective while the subgroup generated is not abelian at all.
--
--   **Formalization note.** In $\mathrm{Homeo}_+(\mathbb{R})$ every non-identity element has infinite order, so the hypothesis is equivalent to $u \neq 1$ and $v \neq 1$; it is stated in the infinite-order form the source uses. Lemma (1.2) of the source is stated for an arbitrary family; only the rank-two case is needed here.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 488, Lemma (1.2), in the rank-two case.

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem freeAbelian_two_of_disjoint_supp {u v : ℝ ≃o ℝ}
    (hu : ∀ k : ℤ, k ≠ 0 → u ^ k ≠ 1) (hv : ∀ k : ℤ, k ≠ 0 → v ^ k ≠ 1)
    (hdisj : Disjoint (supp u) (supp v)) :
    Function.Injective (fun p : ℤ × ℤ => u ^ p.1 * v ^ p.2) := by
  sorry

end BrinSquier
