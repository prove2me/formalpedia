-- Prove2me | Theorems.Thm_Algebra_norm_eq_norm_fst_mul_norm_snd_of_injective
-- name    : Algebra.norm_eq_norm_fst_mul_norm_snd_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/4642b3f9-e22f-5ba6-b7fc-a5f79fa4b827
-- title:
--   Norm multiplicativity along a full-rank injection into B₀ × B₁
-- statement:
--   Let $A$ be a commutative ring which is an integral domain, and let $B$, $B_0$, $B_1$ be commutative $A$-algebras each of which is finite and free as an $A$-module. Suppose given an $A$-algebra homomorphism $\varphi \colon B \to B_0 \times B_1$ (into the product ring) which is injective as a map of sets, and suppose the rank condition $\operatorname{finrank}_A B = \operatorname{finrank}_A B_0 + \operatorname{finrank}_A B_1$ holds. Then for every $b \in B$ one has $$\operatorname{N}_{B/A}(b) = \operatorname{N}_{B_0/A}(\varphi(b)_1)\cdot \operatorname{N}_{B_1/A}(\varphi(b)_2),$$ where $\operatorname{N}$ denotes `Algebra.norm`, the determinant of multiplication by the element regarded as an $A$-linear endomorphism, and $\varphi(b)_1$, $\varphi(b)_2$ are the two components of $\varphi(b)$. No hypothesis is imposed on $b$ (it need not be a unit or a non-zero-divisor), and the rank hypothesis cannot be dropped: the diagonal $A \to A \times A$ gives $a$ on the left and $a^2$ on the right.
--
--   This is the multiplicativity of the algebra norm along a two-component cover: a finite free $A$-algebra $B$ that embeds with full rank into $B_0 \times B_1$ has norm the product of the component norms, extending [`Algebra.norm_prod`](thm.html#Algebra.norm_prod) from the case $B = B_0 \times B_1$. It is used in the construction of norm data on modules over schemes, in [`AlgebraicGeometry.Scheme.Modules.exists_normModule_frameKit_of_isClosedImmersion`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_normModule_frameKit_of_isClosedImmersion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_norm_eq_norm_fst_mul_norm_snd_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.norm_eq_norm_fst_mul_norm_snd_of_injective
    {A B B₀ B₁ : Type*} [CommRing A] [IsDomain A] [CommRing B] [CommRing B₀] [CommRing B₁]
    [Algebra A B] [Algebra A B₀] [Algebra A B₁]
    [Module.Free A B] [Module.Finite A B] [Module.Free A B₀] [Module.Finite A B₀]
    [Module.Free A B₁] [Module.Finite A B₁]
    (φ : B →ₐ[A] B₀ × B₁) (hφ : Function.Injective φ)
    (hrank : Module.finrank A B = Module.finrank A B₀ + Module.finrank A B₁) (b : B) :
    Algebra.norm A b = Algebra.norm A (φ b).1 * Algebra.norm A (φ b).2 := by sorry
