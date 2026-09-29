-- Prove2me | Theorems.Thm_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply
-- name    : AdicCompletion.exists_linearMap_forall_val_apply_eq_mk_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/0e18901a-e0bd-5c1d-8ae9-f796f0eaa27d
-- title:
--   A comparison map widehatHom_A(M,N)toHom_A(M,widehat N)
-- statement:
--   Let $A$ be a commutative ring (in a fixed universe $u$), let $I$ be an ideal of $A$, and let $M$ and $N$ be $A$-modules, again in universe $u$, each given as an additive commutative group with an $A$-module structure. Write $\operatorname{AdicCompletion} I\,P$ for Mathlib's $I$-adic completion of an $A$-module $P$, realised as the submodule of $\prod_n P/(I^n\cdot\top)$ consisting of the families compatible under the transition maps, so that an element $x$ has components $x.\mathrm{val}\,n \in P/(I^nP)$. The theorem asserts that there exists an $A$-linear map $$\theta : \operatorname{AdicCompletion} I\,(M\to_{\mathrm{lin}[A]} N)\longrightarrow \bigl(M\to_{\mathrm{lin}[A]} \operatorname{AdicCompletion} I\,N\bigr)$$ with the following levelwise property: for every $x$ in the completion of $\operatorname{Hom}_A(M,N)$, every $n \in \mathbb{N}$ and every $g \in \operatorname{Hom}_A(M,N)$ whose class modulo $I^n\cdot\top$ equals the $n$-th component $x.\mathrm{val}\,n$, and for every $m \in M$, the $n$-th component of $\theta(x)(m) \in \operatorname{AdicCompletion} I\,N$ is the class of $g(m)$ in $N/(I^n\cdot\top)$. Only existence is asserted here; no uniqueness, injectivity or surjectivity statement is made, and no finiteness or Noetherian hypotheses are imposed.
--
--   This is the standard comparison map from the $I$-adic completion of a Hom module into the Hom module of the target's completion, obtained as the inverse limit of the natural maps $\operatorname{Hom}_A(M,N)/I^n\operatorname{Hom}_A(M,N)\to\operatorname{Hom}_A(M,N/I^nN)$; under Noetherian and finiteness hypotheses it is an isomorphism, but that is not claimed here. It serves the statement [`Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq`](thm.html#Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq), where compatible families of maps into the finite-level quotients are assembled into a single map into the completion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem AdicCompletion.exists_linearMap_forall_val_apply_eq_mk_apply
    {A : Type u} [CommRing A] (I : Ideal A)
    (M N : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    ∃ θ : AdicCompletion I (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] AdicCompletion I N),
      ∀ (x : AdicCompletion I (M →ₗ[A] N)) (n : ℕ) (g : M →ₗ[A] N),
        Submodule.Quotient.mk g = x.val n →
          ∀ m : M, (θ x m).val n = Submodule.Quotient.mk (g m) := by sorry
