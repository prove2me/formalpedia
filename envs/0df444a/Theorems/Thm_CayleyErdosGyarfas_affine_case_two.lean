-- Prove2me | Theorems.Thm_CayleyErdosGyarfas_affine_case_two
-- name    : CayleyErdosGyarfas.affine_case_two
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T02:39:06.444128+00:00
-- url     : https://prove2.me/theorems/1c8f100d-28ab-435e-a24f-fc2bef7aee85
-- title:
--   Case (2) of the proof of Theorem 1.1: the order-five affine case
-- statement:
--   Let $G$ be a group acting faithfully on a field $K$ through an injective homomorphism $\varphi : G \to \operatorname{Sym}(K)$, and suppose $2 \ne 0$ in $K$. Let $S \subseteq G$ and $s, t \in S$ with $s^{-1} \in S$, and let $r \in K^\times$ satisfy $r \ne 1$ and $r^5 = 1$. If
--
--   $$\varphi(s)(z) = r z, \qquad \varphi(t)(z) = r^2 z + 1 \qquad (z \in K),$$
--
--   then $\operatorname{Cay}(G,S)$ contains a symmetric figure-eight. Here $\operatorname{Cay}(G,S)$ has vertex set $G$, distinct $g, h$ being adjacent when $h = gu$ or $g = hu$ for some $u \in S$, and a symmetric figure-eight is a pair of cycles of a common length $2^n$, $n \ge 2$, that meet in exactly one vertex, one a left translate of the other up to the choice of starting vertex (definition `CayleyErdosGyarfas_HasSymmetricFigureEight`).
--
--   This is case (2) of the proof of Theorem 1.1 of the source paper: the quotient of the minimal counterexample by its minimal normal subgroup has order $5$, and the generators are normalized to $s = x$ and $t = \tau_1 x^2$ in the affine group of a finite field.
--
--   **Formalization Note** Neither finiteness of $G$ nor generation by $S$ is assumed, and only $s, s^{-1}, t \in S$ are used; further elements of $S$ only add edges. Since $r \ne 1$ and $r^5 = 1$, the element $r$ has multiplicative order $5$.
-- source:
--   M. C. Burkhart, Odd-ordered Cayley graphs satisfy Erdős–Gyárfás, arXiv:2611.05060v1 (https://arxiv.org/abs/2611.05060v1), §2, pp. 4–5, proof of Theorem 1.1, case (2). Lean statement: https://github.com/burkh4rt/Cayley-Erdos-Gyarfas-Formalized/blob/111aa033acfab934208ce6b2e0cebecacfd6bd24/CayleyErdosGyarfas/AffineCaseTwo.lean#L218-L259 (Palomar entry PALOMAR-2026-11-04-000015).

import Definitions.Def_CayleyErdosGyarfas_HasSymmetricFigureEight
import Mathlib.Algebra.Field.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace CayleyErdosGyarfas

theorem affine_case_two {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S) (hsi : s⁻¹ ∈ S)
    (r : Kˣ) (hr : (r:K) ≠ 1) (hr5 : (r:K)^5 = 1) (h2 : (2:K) ≠ 0)
    (hsact : ∀ z, φ s z = (r:K)*z)
    (htact : ∀ z, φ t z = (r:K)^2*z+1) :
    HasSymmetricFigureEight S := by sorry

end CayleyErdosGyarfas
