-- Prove2me | Theorems.Thm_AlgebraicGeometry_flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk
-- name    : AlgebraicGeometry.flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/ae2917af-6d0c-5d44-b58d-7ed20f9c956c
-- title:
--   Flatness of R/J⊗_Rmathcal O_{Z,z} from flat base change
-- statement:
--   Let $R$ be a commutative ring, $J\subseteq R$ an ideal, and let $f : Z \to \operatorname{Spec} R$ be a morphism from a scheme $Z$ to the affine scheme of $R$. Assume, as a typeclass hypothesis, that the second projection from the fibre product $Z \times_{\operatorname{Spec} R} \operatorname{Spec}(R/J)$ to $\operatorname{Spec}(R/J)$ — the pullback of $f$ along $\operatorname{Spec}$ of the quotient map $R \to R/J$ — is a flat morphism of schemes. Let $z$ be any point of $Z$, with no condition imposed on $z$. Give the stalk $\mathcal O_{Z,z}$ its $R$-algebra structure through $f$, namely the ring homomorphism obtained by composing the inverse of the canonical isomorphism $R \cong \Gamma(\operatorname{Spec} R)$, the map $f^{\sharp}$ on global sections, and the germ map $\Gamma(Z,\top) \to \mathcal O_{Z,z}$. Then $(R/J) \otimes_R \mathcal O_{Z,z}$ is a flat module over $R/J$.
--
--   This is the stalkwise form of flatness of a base change: flatness of $f$ after reduction modulo $J$ is transferred to the local rings of $Z$ in the form of flatness of $R/J \otimes_R \mathcal O_{Z,z}$ over $R/J$. It feeds the criterion [`AlgebraicGeometry.flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper`](thm.html#AlgebraicGeometry.flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper), which deduces flatness of a proper morphism from flatness of its base changes along the quotients by powers of a maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk
    {R : Type u} [CommRing R] (J : Ideal R) {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of R))
    [Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))] (z : ↥Z) :
    letI : Algebra R ↑(Z.presheaf.stalk z) :=
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ Z.presheaf.germ ⊤ z trivial).hom).toAlgebra
    Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] ↑(Z.presheaf.stalk z)) := by sorry
