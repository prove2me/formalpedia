-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_spec_map_comp_eq_of_forall_spec_map_comp_eq_of_forall_mem_iff
-- name    : AlgebraicGeometry.exists_spec_map_comp_eq_of_forall_spec_map_comp_eq_of_forall_mem_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/f9338352-29c9-5043-b30c-641695f98f29
-- title:
--   Invariant Ω-points factor through the fixed subfield
-- statement:
--   Let $\Omega$ be a field (in the lowest universe), $X$ a scheme (also in the lowest universe), and $x\colon \operatorname{Spec}\Omega \to X$ a morphism of schemes. Let $S$ be a set of ring automorphisms of $\Omega$ — no closure properties are imposed on $S$ — and assume that $x$ is invariant under $S$, in the sense that for every $\sigma \in S$ the morphism $\operatorname{Spec}(\sigma)$ followed by $x$ equals $x$. Let $F$ be a subfield of $\Omega$ which is exactly the set of $S$-invariant elements: for all $a \in \Omega$, $a$ lies in $F$ if and only if $\sigma a = a$ for every $\sigma \in S$. The conclusion asserts the existence of a morphism of schemes $y \colon \operatorname{Spec} F \to X$ such that the morphism $\operatorname{Spec}(F \hookrightarrow \Omega)$ induced by the inclusion of $F$ in $\Omega$, followed by $y$, equals $x$. Thus an $S$-invariant $\Omega$-point of $X$ is the base change along $F \subseteq \Omega$ of an $F$-point; note that $y$ is only asserted to exist, with no uniqueness claim.
--
--   This is the elementary form of Galois descent for points of a scheme: a point with values in a field, invariant under a set of automorphisms, comes from a point with values in the fixed subfield. It is used to recognise $I$-invariant $\overline{\mathbb{Q}}$-points of modular Jacobians and of models of modular curves as points over the fixed field $\overline{\mathbb{Q}}^{I}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_spec_map_comp_eq_of_forall_spec_map_comp_eq_of_forall_mem_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_spec_map_comp_eq_of_forall_spec_map_comp_eq_of_forall_mem_iff
    (Ω : Type) [Field Ω] (X : Scheme.{0}) (x : Spec (CommRingCat.of Ω) ⟶ X)
    (S : Set (Ω ≃+* Ω)) (hx : ∀ σ ∈ S, Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x = x)
    (F : Subfield Ω) (hF : ∀ a : Ω, a ∈ F ↔ ∀ σ ∈ S, σ a = a) :
    ∃ y : Spec (CommRingCat.of ↥F) ⟶ X, Spec.map (CommRingCat.ofHom F.subtype) ≫ y = x := by sorry
