-- Prove2me | Theorems.Thm_AddMonoidHom_natCard_sq_le_of_isotropic
-- name    : AddMonoidHom.natCard_sq_le_of_isotropic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/33535e3c-c0dc-5f3e-a88b-3a2432c1381d
-- title:
--   Isotropic subgroups of a left-nondegenerate pairing: #K² ≤ #V
-- statement:
--   Let $V$ be a finite additive abelian group and $Q$ an arbitrary additive abelian group, and let $\beta \colon V \to (V \to Q)$ be a biadditive map (an additive monoid homomorphism from $V$ to the group of additive homomorphisms $V \to Q$), so $\beta$ is a $Q$-valued pairing on $V$. Assume $\beta$ is nondegenerate on the left: if $\beta(v) = 0$ as a homomorphism $V \to Q$, that is $\beta(v, w) = 0$ for all $w$, then $v = 0$. Assume moreover that for every nonzero natural number $n$ the set $\{x \in Q : n \cdot x = 0\}$ of $n$-torsion points of $Q$ has extended cardinality at most $n$; this holds for instance for $Q = \mathbb{Q}/\mathbb{Z}$, $\mathbb{R}/\mathbb{Z}$ or $\mathbb{Z}/m\mathbb{Z}$ and for subgroups of these. Finally let $K$ be an additive subgroup of $V$ that is isotropic for $\beta$, meaning $\beta(k, k') = 0$ for all $k, k' \in K$. The conclusion is the inequality of natural cardinalities $(\#K)^2 \le \#V$.
--
--   This is the elementary counting bound behind the statement that an isotropic subgroup for a nondegenerate pairing on a finite abelian group has order at most $\sqrt{\#V}$, obtained by comparing $K$ with the orthogonal complement $K^{\perp}$. It is used in the comparison of Hecke lattices modulo $\ell$, namely by [`ModularCurve.natCard_heckeLatticeAlgebra_quotient_le_natCard_image_reductionModL_heckeTorsion_span_sup`](thm.html#ModularCurve.natCard_heckeLatticeAlgebra_quotient_le_natCard_image_reductionModL_heckeTorsion_span_sup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidHom_natCard_sq_le_of_isotropic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddMonoidHom.natCard_sq_le_of_isotropic
    {V Q : Type*} [AddCommGroup V] [Finite V] [AddCommGroup Q]
    (β : V →+ V →+ Q) (hβ : ∀ v, β v = 0 → v = 0)
    (hQ : ∀ n : ℕ, n ≠ 0 → {x : Q | n • x = 0}.encard ≤ n)
    (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
    Nat.card K ^ 2 ≤ Nat.card V := by sorry
