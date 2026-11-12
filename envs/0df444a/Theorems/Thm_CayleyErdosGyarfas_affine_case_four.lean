-- Prove2me | Theorems.Thm_CayleyErdosGyarfas_affine_case_four
-- name    : CayleyErdosGyarfas.affine_case_four
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T02:39:21.4959+00:00
-- url     : https://prove2.me/theorems/d89d4b8b-f4be-459a-a4af-a9a0d278efd4
-- title:
--   Case (4) of the proof of Theorem 1.1: a generator acting by translation
-- statement:
--   Let $G$ be a group of odd order acting faithfully on a field $K$ through an injective homomorphism $\varphi : G \to \operatorname{Sym}(K)$, and suppose $2 \ne 0$ in $K$. Let $S \subseteq G$ be closed under inverses, let $s, t \in S$, and let $r \in K$ with $r \ne 0$ and $r \ne 1$. If
--
--   $$\varphi(s)(z) = r z, \qquad \varphi(t)(z) = z + 1 \qquad (z \in K),$$
--
--   then $\operatorname{Cay}(G,S)$ contains a symmetric figure-eight. Here $\operatorname{Cay}(G,S)$ has vertex set $G$, distinct $g, h$ being adjacent when $h = gu$ or $g = hu$ for some $u \in S$, and a symmetric figure-eight is a pair of cycles of a common length $2^n$, $n \ge 2$, that meet in exactly one vertex, one a left translate of the other up to the choice of starting vertex (definition `CayleyErdosGyarfas_HasSymmetricFigureEight`).
--
--   This is case (4) of the proof of Theorem 1.1 of the source paper: one of the two generators has trivial image modulo the minimal normal subgroup, and the generators are normalized to $s = x$ and $t = \tau_1$ in the affine group of a finite field.
--
--   **Formalization Note** Odd order is `Odd (Nat.card G)`; since `Nat.card` is $0$ on infinite types, this hypothesis also forces $G$ to be finite. Generation by $S$ is not assumed.
-- source:
--   M. C. Burkhart, Odd-ordered Cayley graphs satisfy Erdős–Gyárfás, arXiv:2611.05060v1 (https://arxiv.org/abs/2611.05060v1), §2, p. 5, proof of Theorem 1.1, case (4). Lean statement: https://github.com/burkh4rt/Cayley-Erdos-Gyarfas-Formalized/blob/111aa033acfab934208ce6b2e0cebecacfd6bd24/CayleyErdosGyarfas/AffineCaseFour.lean#L355-L427 (Palomar entry PALOMAR-2026-11-04-000015).

import Definitions.Def_CayleyErdosGyarfas_HasSymmetricFigureEight
import Mathlib.Algebra.Field.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace CayleyErdosGyarfas

theorem affine_case_four {G K : Type*} [Group G] [Field K]
    (hodd : Odd (Nat.card G))
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (r : K) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (h2 : (2:K) ≠ 0)
    (hsact : ∀ z, φ s z = r*z) (htact : ∀ z, φ t z = z+1) :
    HasSymmetricFigureEight S := by sorry

end CayleyErdosGyarfas
