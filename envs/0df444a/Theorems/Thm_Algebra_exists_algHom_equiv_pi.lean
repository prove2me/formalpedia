-- Prove2me | Theorems.Thm_Algebra_exists_algHom_equiv_pi
-- name    : Algebra.exists_algHom_equiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/5dc26ab2-d949-5fd0-b7d8-588a3fb40282
-- title:
--   A finite free A-algebra representing a product of Hom-functors
-- statement:
--   Let $A$ be a commutative ring, let $\iota$ be a finite index type, and let $H : \iota \to \mathrm{Type}$ be a family of commutative rings, each equipped with an $A$-algebra structure making it finite and free as an $A$-module. The assertion is the existence of a type $W$ (in the same universe as $A$ and the $H_i$) carrying a commutative ring structure and an $A$-algebra structure, such that $W$ is finite and free as an $A$-module, together with a family $e$ of bijections
--   $$e_T : (W \to_{A\text{-alg}} T) \;\simeq\; \prod_{i} (H_i \to_{A\text{-alg}} T),$$
--   one for every type $T$ in that universe equipped with a commutative ring structure and an $A$-algebra structure, which is natural in $T$ in the following sense: for all such $T$, $T'$, every $A$-algebra homomorphism $u : T \to T'$ and every $A$-algebra homomorphism $f : W \to T$, one has $e_{T'}(u \circ f) = (i \mapsto u \circ e_T(f)\,i)$. Thus the functor of points of $W$ on commutative $A$-algebras is identified with the product of those of the $H_i$, compatibly with postcomposition; no formula for $W$ is part of the statement.
--
--   This records that a finite family of finite free commutative $A$-algebras has a coproduct in commutative $A$-algebras which is again finite and free over $A$, i.e. that $\prod_i \operatorname{Spec} H_i$ is again affine, finite and free over $A$. It is used in the construction of the Weil restriction-type base change statement [`Algebra.finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi`](thm.html#Algebra.finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_algHom_equiv_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.exists_algHom_equiv_pi
    (A : Type u) [CommRing A] (ι : Type) [Finite ι]
    (H : ι → Type u) [∀ i, CommRing (H i)] [∀ i, Algebra A (H i)]
    [∀ i, Module.Finite A (H i)] [∀ i, Module.Free A (H i)] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra A W),
      Module.Finite A W ∧ Module.Free A W ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (∀ i, H i →ₐ[A] T),
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
          (f : W →ₐ[A] T),
          e T' (u.comp f) = fun i => u.comp (e T f i) := by sorry
