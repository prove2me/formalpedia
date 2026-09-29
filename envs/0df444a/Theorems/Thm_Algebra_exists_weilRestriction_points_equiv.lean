-- Prove2me | Theorems.Thm_Algebra_exists_weilRestriction_points_equiv
-- name    : Algebra.exists_weilRestriction_points_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/c5a354cb-bbfa-57b3-af6c-d013af7668dd
-- title:
--   Representability of Weil restriction for affine schemes
-- statement:
--   Let $A$ and $B$ be commutative rings in a fixed universe with $B$ an $A$-algebra that is finite and free as an $A$-module, and let $H$ be a commutative ring equipped with a $B$-algebra structure. The assertion is the existence of a type $W$ in the same universe, carrying a commutative ring structure and an $A$-algebra structure, together with a family of bijections $e_T \colon \operatorname{Hom}_{A\text{-alg}}(W, T) \;\simeq\; \operatorname{Hom}_{B\text{-alg}}(H,\, B \otimes_A T)$, one for every commutative ring $T$ with an $A$-algebra structure, and the naturality condition: for all commutative $A$-algebras $T$, $T'$, every $A$-algebra homomorphism $u \colon T \to T'$ and every $A$-algebra homomorphism $f \colon W \to T$, one has $e_{T'}(u \circ f) = (\mathrm{id}_B \otimes u) \circ e_T(f)$, where $\mathrm{id}_B \otimes u \colon B \otimes_A T \to B \otimes_A T'$ is the induced map of $B$-algebras. Thus the functor sending $T$ to the $B$-algebra homomorphisms $H \to B \otimes_A T$ is represented by $W$; no finiteness assumption is placed on $H$.
--
--   This is the affine, functor-of-points form of representability of the Weil restriction $\operatorname{Res}_{B/A}\operatorname{Spec} H$ along a finite free extension $A \to B$. It is used to obtain the finite-type refinement of the construction and the version producing a Hopf algebra structure, i.e. Weil restriction of affine group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_weilRestriction_points_equiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.exists_weilRestriction_points_equiv
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (H : Type u) [CommRing H] [Algebra B H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra A W),
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)),
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
          (f : W →ₐ[A] T), e T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f) := by sorry
