-- Prove2me | Theorems.Thm_Algebra_Etale_exists_sum_mul_smul_eq_ite_of_isLocalRing
-- name    : Algebra.Etale.exists_sum_mul_smul_eq_ite_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/b6b68b0b-0369-5abc-9d5f-a92f3ddc3b31
-- title:
--   Étale local extensions with full automorphism group are Galois
-- statement:
--   Let $W$ and $W'$ be commutative local rings and let $W'$ be a $W$-algebra which is finite and flat as a $W$-module, for which the structure map acts faithfully (so that $W \to W'$ is injective), and which is étale over $W$. Let $\Gamma$ be a finite group acting on $W'$ by ring automorphisms, the action commuting with the $W$-action on $W'$, so that $\Gamma$ acts by $W$-algebra automorphisms. Assume two hypotheses: first, that an element $w' \in W'$ satisfies $\gamma \cdot w' = w'$ for every $\gamma \in \Gamma$ if and only if $w'$ lies in the image of the structure map $W \to W'$, i.e. the ring of $\Gamma$-invariants of $W'$ is exactly $W$; second, that the order of $\Gamma$ equals the rank $\operatorname{finrank}_W W'$ of $W'$ as a $W$-module. The conclusion is the existence of a natural number $n$ and two families $x, y \colon \{0,\dots,n-1\} \to W'$ such that for every $\gamma \in \Gamma$ one has $\sum_{i} x_i \cdot (\gamma \cdot y_i) = 1$ if $\gamma = 1$ and $\sum_{i} x_i \cdot (\gamma \cdot y_i) = 0$ otherwise. The length $n$ is only asserted to exist, with no bound claimed.
--
--   The conclusion is the criterion of Chase–Harrison–Rosenberg for $W \to W'$ to be a Galois extension with group $\Gamma$: the existence of such elements $x_i, y_i$ is equivalent to the map $W' \otimes_W W' \to \prod_{\Gamma} W'$, $a \otimes b \mapsto (a\,\gamma b)_\gamma$, being an isomorphism, and is the form in which the Galois property is used downstream. It serves [`IsLocalRing.exists_crossingPresentation_of_baseChange_of_forall_map_span_eq`](thm.html#IsLocalRing.exists_crossingPresentation_of_baseChange_of_forall_map_span_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_exists_sum_mul_smul_eq_ite_of_isLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.Etale.exists_sum_mul_smul_eq_ite_of_isLocalRing
    {W W' : Type*} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    [Algebra W W'] [Module.Finite W W'] [Module.Flat W W'] [FaithfulSMul W W'] [Algebra.Etale W W']
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
    (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') ↔ w' ∈ Set.range (algebraMap W W'))
    (hcard : Fintype.card Γ = Module.finrank W W') :
    ∃ (n : ℕ) (x y : Fin n → W'), ∀ γ : Γ, ∑ i, x i * γ • y i = if γ = 1 then 1 else 0 := by sorry
