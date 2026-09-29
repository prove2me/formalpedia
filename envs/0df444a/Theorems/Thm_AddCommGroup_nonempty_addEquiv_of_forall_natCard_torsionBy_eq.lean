-- Prove2me | Theorems.Thm_AddCommGroup_nonempty_addEquiv_of_forall_natCard_torsionBy_eq
-- name    : AddCommGroup.nonempty_addEquiv_of_forall_natCard_torsionBy_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/9234f3e6-28f1-583b-b2bf-a4b8733e144c
-- title:
--   Equal N-torsion counts force isomorphism of finite abelian groups
-- statement:
--   Let $A$ and $B$ be additive commutative groups, in possibly distinct universes, each assumed finite. Regard both as $\mathbb{Z}$-modules in the canonical way, so that for an integer $n$ the submodule `Submodule.torsionBy ℤ A n` is the subgroup $\{a \in A : n \cdot a = 0\}$ of $n$-torsion elements. The hypothesis is that for every natural number $N$ the $N$-torsion subgroups of $A$ and of $B$, where $N$ is taken as the integer $(N : \mathbb{Z})$, have the same cardinality: $\mathrm{Nat.card}\,\{a \in A : Na = 0\} = \mathrm{Nat.card}\,\{b \in B : Nb = 0\}$. Note that the case $N = 0$ of this hypothesis already gives $\#A = \#B$. The conclusion is that the type `A ≃+ B` of additive group isomorphisms from $A$ to $B$ is nonempty, that is, $A$ and $B$ are isomorphic as abelian groups; the statement asserts the existence of such an isomorphism rather than exhibiting a particular one.
--
--   This is the counting form of the uniqueness part of the structure theorem for finite abelian groups (Frobenius–Stickelberger): the sequence of torsion counts $\#A[N]$ determines the elementary divisors, hence the isomorphism class. It is used in the proof of [`AddEquiv.nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod`](thm.html#AddEquiv.nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_nonempty_addEquiv_of_forall_natCard_torsionBy_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem AddCommGroup.nonempty_addEquiv_of_forall_natCard_torsionBy_eq
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]
    (h : ∀ N : ℕ, Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) = Nat.card (Submodule.torsionBy ℤ B (N : ℤ))) :
    Nonempty (A ≃+ B) := by sorry
