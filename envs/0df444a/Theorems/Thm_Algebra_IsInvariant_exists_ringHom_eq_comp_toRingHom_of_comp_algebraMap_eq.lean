-- Prove2me | Theorems.Thm_Algebra_IsInvariant_exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq
-- name    : Algebra.IsInvariant.exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/471d75ec-c896-5955-b630-db9cf8907b4f
-- title:
--   Two Ω-points agreeing on an invariant subring are G-conjugate
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra, and let $G$ be a finite group acting on $B$ by ring automorphisms (a `MulSemiringAction`) in such a way that the $G$-action commutes with the $A$-scalar multiplication on $B$, so that $G$ fixes the image of $A$ pointwise. Assume the action is invariant in the sense of `Algebra.IsInvariant A B G`: every element of $B$ fixed by all of $G$ lies in the image of the structure map $A \to B$. Let $\Omega$ be a field and let $\varphi_1, \varphi_2 \colon B \to \Omega$ be ring homomorphisms whose composites with $\mathrm{algebraMap} : A \to B$ agree, i.e. $\varphi_1$ and $\varphi_2$ restrict to the same map on (the image of) $A$. The conclusion is that there exists $g \in G$ with $\varphi_2 = \varphi_1 \circ \sigma_g$, where $\sigma_g \colon B \to B$ is the ring homomorphism given by the action of $g$; equivalently, $\varphi_2(b) = \varphi_1(g \cdot b)$ for all $b \in B$. No finiteness, flatness or reducedness hypothesis on $B$ over $A$ is imposed beyond the invariance condition, and $\Omega$ is an arbitrary field, not assumed algebraically closed.
--
--   This is the pointwise half of the classical statement that $\operatorname{Spec}(B^G)$ is the quotient of $\operatorname{Spec} B$ by a finite group $G$: any two $\Omega$-valued points of $\operatorname{Spec} B$ lying over the same $\Omega$-valued point of the invariant subring belong to a single $G$-orbit. It is used, in the form [`CerednikDrinfeld.QM.exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed`](thm.html#CerednikDrinfeld.QM.exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed), to identify geometric points of a quotient of a moduli scheme by a finite group with orbits of geometric points of the scheme itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsInvariant_exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.IsInvariant.exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    {Ω : Type*} [Field Ω] (φ₁ φ₂ : B →+* Ω)
    (h : φ₁.comp (algebraMap A B) = φ₂.comp (algebraMap A B)) :
    ∃ g : G, φ₂ = φ₁.comp (MulSemiringAction.toRingHom G B g) := by sorry
