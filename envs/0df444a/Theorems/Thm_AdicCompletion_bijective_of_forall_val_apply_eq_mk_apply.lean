-- Prove2me | Theorems.Thm_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply
-- name    : AdicCompletion.bijective_of_forall_val_apply_eq_mk_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/56eac84a-92b7-5e96-afe8-308e0495d9cb
-- title:
--   Adic completion of a Hom module between finite modules
-- statement:
--   Let $A$ be a commutative Noetherian ring and $I \subseteq A$ an ideal, and let $M$ and $N$ be finite $A$-modules (all three types in a single universe, with the usual module structures). Write $\widehat{(-)}$ for the $I$-adic completion, realised as the submodule of compatible families in $\prod_{n} (-)/I^{n}(-)$, so that an element $x$ of a completion has components $x.\mathrm{val}\, n$ in the level-$n$ quotient. Suppose given an $A$-linear map $\theta : \widehat{\operatorname{Hom}_A(M,N)} \to \operatorname{Hom}_A(M, \widehat{N})$ subject to the following levelwise compatibility: for every $x \in \widehat{\operatorname{Hom}_A(M,N)}$, every $n \in \mathbb{N}$ and every $A$-linear $g : M \to N$ whose class modulo $I^{n}\operatorname{Hom}_A(M,N)$ equals the $n$-th component of $x$, and for every $m \in M$, the $n$-th component of $\theta(x)(m)$ is the class of $g(m)$ in $N/I^{n}N$. The conclusion is that $\theta$ is bijective. Thus the statement is not the construction of the comparison map but the assertion that any $A$-linear map with this levelwise description is an isomorphism of $A$-modules.
--
--   This is the standard identification $\widehat{\operatorname{Hom}_A(M,N)} \cong \operatorname{Hom}_A(M,\widehat{N})$ for finite modules over a Noetherian ring, in the form of a recognition criterion for a candidate comparison map. It is used in the proof of [`Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq`](thm.html#Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq), where a compatible system of maps into the finite quotients of $N$ has to be assembled into a single map over the completion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem AdicCompletion.bijective_of_forall_val_apply_eq_mk_apply
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N]
    (θ : AdicCompletion I (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] AdicCompletion I N))
    (hθ : ∀ (x : AdicCompletion I (M →ₗ[A] N)) (n : ℕ) (g : M →ₗ[A] N),
      Submodule.Quotient.mk g = x.val n →
        ∀ m : M, (θ x m).val n = Submodule.Quotient.mk (g m)) :
    Function.Bijective θ := by sorry
