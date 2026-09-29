-- Prove2me | Theorems.Thm_Algebra_finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi
-- name    : Algebra.finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/0d9085a4-6768-552a-9c63-1e32032c28b6
-- title:
--   Base change of a split Weil restriction is finite free
-- statement:
--   Let $A$, $B$, $H$, $W$, $A'$ be commutative rings in a fixed universe, with $B$ an $A$-algebra, $H$ a $B$-algebra that is finite and free as a $B$-module, and $W$ and $A'$ both $A$-algebras. Assume given a family of bijections $e_T \colon \operatorname{Hom}_{A\text{-alg}}(W,T) \simeq \operatorname{Hom}_{B\text{-alg}}(H, B \otimes_A T)$, one for each commutative $A$-algebra $T$ in that universe, which is natural in the following explicit sense: for every $A$-algebra map $u \colon T \to T'$ and every $f \colon W \to T$, one has $e_{T'}(u \circ f) = (\mathrm{id}_B \otimes u) \circ e_T(f)$. Thus $\operatorname{Spec} W$ represents the Weil restriction of $\operatorname{Spec} H$ along $A \to B$. Assume furthermore that $B$ splits over $A'$: there are a natural number $d$ and an isomorphism of $A'$-algebras $\varphi \colon A' \otimes_A B \cong \prod_{i \in \mathrm{Fin}\,d} A'$. The conclusion is that $A' \otimes_A W$ is finite and free as an $A'$-module.
--
--   This is the split case of the standard fact that the Weil restriction along a finite free extension is again finite free, in the representability formulation: after a base change splitting $B$ into $d$ copies, the restriction becomes a $d$-fold tensor product of base changes of $H$. It feeds into [`Algebra.finite_and_flat_of_weilRestriction_points_equiv`](thm.html#Algebra.finite_and_flat_of_weilRestriction_points_equiv), where finiteness and flatness of a Weil restriction are deduced by descent from such a splitting base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (H : Type u) [CommRing H] [Algebra B H] [Module.Finite B H] [Module.Free B H]
    (W : Type u) [CommRing W] [Algebra A W]
    (e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)))
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
      (f : W →ₐ[A] T), e T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f))
    (A' : Type u) [CommRing A'] [Algebra A A'] (d : ℕ) (φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')) :
    Module.Finite A' (A' ⊗[A] W) ∧ Module.Free A' (A' ⊗[A] W) := by sorry
