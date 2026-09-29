-- Prove2me | Theorems.Thm_Algebra_IsInvariant_exists_forall_smul_eq_and_sub_mem_of_le_inertia
-- name    : Algebra.IsInvariant.exists_forall_smul_eq_and_sub_mem_of_le_inertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/a886f455-7406-5c23-9d4e-3059a8d55419
-- title:
--   Subgroup of inertia: invariants surject onto the residue field
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra, and let $G$ be a finite group acting on $B$ by ring automorphisms in a way that commutes with the $A$-action, such that $B$ is invariant over $A$ in the sense of `Algebra.IsInvariant A B G`: every $G$-fixed element of $B$ lies in the image of $A$. Let $P$ be a maximal ideal of $A$ and $Q$ a maximal ideal of $B$ lying over $P$, and assume that the residue field extension $(B/Q)/(A/P)$ is separable. Let $H$ be a subgroup of $G$ contained in the inertia subgroup `Q.inertia G` of $Q$, i.e. each $h \in H$ satisfies $h \cdot x - x \in Q$ for all $x \in B$. Then for every $b \in B$ there exists $b' \in B$ with $h \cdot b' = b'$ for all $h \in H$ and $b - b' \in Q$. Equivalently, the ring of $H$-invariants of $B$ surjects onto the residue field $B/Q$.
--
--   This is the standard fact that the invariants under a subgroup of the inertia group already see the whole residue field, when the residue extension is separable (as in the classical description of the residue field of the inertia field). It is used in the construction of a subalgebra of fixed points of inertia which is étale and local with prescribed rank over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsInvariant_exists_forall_smul_eq_and_sub_mem_of_le_inertia.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem Algebra.IsInvariant.exists_forall_smul_eq_and_sub_mem_of_le_inertia
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)]
    (H : Subgroup G) (hH : H ≤ Q.inertia G) (b : B) :
    ∃ b' : B, (∀ h ∈ H, h • b' = b') ∧ b - b' ∈ Q := by sorry
