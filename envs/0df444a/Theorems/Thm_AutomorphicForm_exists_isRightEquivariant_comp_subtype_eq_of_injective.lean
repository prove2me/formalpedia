-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective
-- name    : AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/9a37505d-d9fe-5585-95e2-647c4644b3c2
-- title:
--   Right-equivariant maps into ℂ^G extend from subrepresentations
-- statement:
--   Let $H$ and $G$ be groups, let $W$ be a complex vector space, let $\iota : H \to G$ be a group homomorphism which is injective as a function, and let $\rho$ be a representation of $H$ on $W$ over $\mathbb{C}$. Let $A$ be a $\mathbb{C}$-subspace of $W$ which is $\rho$-stable in the sense that $\rho(k)a \in A$ whenever $k \in H$ and $a \in A$, and let $T_A : A \to (G \to \mathbb{C})$ be a $\mathbb{C}$-linear map into the space of all complex-valued functions on $G$ satisfying the right-equivariance $T_A(\rho(k)a)(x) = T_A(a)(x\,\iota(k))$ for all $k \in H$, $a \in A$ and $x \in G$ (the left-hand side being formed using the stability hypothesis). The conclusion asserts the existence of a $\mathbb{C}$-linear map $T : W \to (G \to \mathbb{C})$ which is right-equivariant in the same sense, i.e. $T(\rho(k)v)(x) = T(v)(x\,\iota(k))$ for all $k \in H$, $v \in W$, $x \in G$ — this being the predicate `IsRightEquivariant ι ρ T` — and whose restriction to $A$, i.e. the composite of the inclusion $A \hookrightarrow W$ with $T$, equals $T_A$.
--
--   This is the injectivity of $\mathbb{C}^G$ as a $\mathbb{C}[H]$-module when $H$ acts on $G$ freely by right translation through an injective $\iota$: such a module is co-induced from the trivial subgroup, so equivariant maps extend from subrepresentations (Eckmann–Shapiro). It is used in the treatment of archimedean types of automorphic forms, where the isotypic piece attached to a finite-dimensional representation of a compact subgroup is defined as the span of the images of all right-equivariant maps; it is cited by the results identifying such isotypic pieces and by the stability statements for convolution operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective
    {H G : Type*} [Group H] [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H W)
    (A : Submodule ℂ W) (hA : ∀ (k : H) (a : W), a ∈ A → ρ k a ∈ A)
    (TA : ↥A →ₗ[ℂ] (G → ℂ))
    (hTA : ∀ (k : H) (a : ↥A) (x : G), TA ⟨ρ k a, hA k a a.2⟩ x = TA a (x * ι k)) :
    ∃ T : W →ₗ[ℂ] (G → ℂ), IsRightEquivariant ι ρ T ∧ T ∘ₗ A.subtype = TA := by sorry
