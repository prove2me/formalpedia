-- Prove2me | Theorems.Thm_Algebra_finite_and_flat_of_weilRestriction_points_equiv
-- name    : Algebra.finite_and_flat_of_weilRestriction_points_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/1c7a6817-3a03-5960-ad92-1d767e4e1550
-- title:
--   Weil restriction along a finite étale extension is finite flat
-- statement:
--   Let $A$ and $B$ be commutative rings in a fixed universe with $B$ an $A$-algebra that is finite and free as an $A$-module and étale over $A$; let $H$ be a commutative $B$-algebra that is finite and free as a $B$-module; and let $W$ be a commutative $A$-algebra. Suppose given, for every commutative $A$-algebra $T$ in the same universe, a bijection $e_T \colon \operatorname{Hom}_{A\text{-alg}}(W,T) \to \operatorname{Hom}_{B\text{-alg}}(H, B \otimes_A T)$, and suppose these bijections are natural in $T$ in the following sense: for all commutative $A$-algebras $T, T'$, every $A$-algebra map $u \colon T \to T'$ and every $A$-algebra map $f \colon W \to T$, one has $e_{T'}(u \circ f) = (\mathrm{id}_B \otimes u) \circ e_T(f)$, where $\mathrm{id}_B \otimes u \colon B \otimes_A T \to B \otimes_A T'$ is the base change of $u$. The conclusion is that $W$ is finite as an $A$-module and flat as an $A$-module. Thus an $A$-algebra representing the Weil restriction along $A \to B$ of the finite free $B$-algebra $H$ is automatically finite and flat over $A$.
--
--   This is the ring-theoretic form of the statement that the Weil restriction of a finite locally free scheme along a finite étale morphism is again finite locally free; the hypotheses say precisely that $\operatorname{Spec} W$ represents the Weil restriction functor $T \mapsto \operatorname{Hom}_{B\text{-alg}}(H, B \otimes_A T)$. It is used in the construction of Weil restrictions of Hopf algebras along étale extensions, via [`HopfAlgebra.exists_weilRestriction_of_etale`](thm.html#HopfAlgebra.exists_weilRestriction_of_etale).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_finite_and_flat_of_weilRestriction_points_equiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.finite_and_flat_of_weilRestriction_points_equiv
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Algebra.Etale A B]
    (H : Type u) [CommRing H] [Algebra B H] [Module.Finite B H] [Module.Free B H]
    (W : Type u) [CommRing W] [Algebra A W]
    (e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)))
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
      (f : W →ₐ[A] T), e T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f)) :
    Module.Finite A W ∧ Module.Flat A W := by sorry
