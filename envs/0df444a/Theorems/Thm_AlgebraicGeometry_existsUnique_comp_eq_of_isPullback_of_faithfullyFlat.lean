-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
-- name    : AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/a706a3e3-8d0e-531b-8355-e55676870125
-- title:
--   Descent of morphisms along a faithfully flat affine base change
-- statement:
--   Let $S \to S'$ be a homomorphism of commutative rings making $S'$ a faithfully flat $S$-module, and write $\iota = \operatorname{Spec}$ of this homomorphism, $\iota_L, \iota_R : \operatorname{Spec}(S' \otimes_S S') \to \operatorname{Spec} S'$ for the spectra of the two coprojections $S' \to S' \otimes_S S'$ (the left ring homomorphism `Algebra.TensorProduct.includeLeftRingHom` and the right inclusion `Algebra.TensorProduct.includeRight`). Let $T, T', T''$ be schemes with structure morphisms $t : T \to \operatorname{Spec} S$, $t' : T' \to \operatorname{Spec} S'$ and $t'' : T'' \to \operatorname{Spec}(S' \otimes_S S')$, and let $p : T' \to T$, $q_1, q_2 : T'' \to T'$ be morphisms. Assume the square formed by $p$, $t'$, $t$, $\iota$ is cartesian (so $T'$ is the base change of $T$ to $S'$), that the square formed by $q_1$, $t''$, $t'$, $\iota_L$ is cartesian, that the square formed by $q_2$, $t''$, $t'$, $\iota_R$ is cartesian, and that $q_1$ followed by $p$ equals $q_2$ followed by $p$. Then for every scheme $Y$ and every morphism $\varphi' : T' \to Y$ with $q_1$ followed by $\varphi'$ equal to $q_2$ followed by $\varphi'$, there is exactly one morphism $\varphi : T \to Y$ such that $p$ followed by $\varphi$ equals $\varphi'$.
--
--   This is the descent of morphisms of schemes along the fpqc covering obtained by a faithfully flat affine base change: representable functors are sheaves for such coverings, with no finiteness or separatedness hypothesis on the source $T$ or the target $Y$. It is used in the theory of polarised abelian schemes and their moduli, for instance to descend isomorphisms and to transfer the fine moduli property along a faithfully flat base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    {Y : Scheme.{u}} (φ' : T' ⟶ Y) (hφ' : q₁ ≫ φ' = q₂ ≫ φ') :
    ∃! φ : T ⟶ Y, p ≫ φ = φ' := by sorry
