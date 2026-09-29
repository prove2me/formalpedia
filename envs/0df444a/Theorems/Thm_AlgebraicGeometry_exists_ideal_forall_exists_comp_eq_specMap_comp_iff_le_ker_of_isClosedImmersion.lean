-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion
-- name    : AlgebraicGeometry.exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/1edd8db6-9b7c-5064-b808-a5509eb52dab
-- title:
--   Incidence ideal of a closed immersion and a point
-- statement:
--   Let $R$ be a commutative ring, let $X$ and $Z$ be schemes, let $\iota : Z \to X$ be a closed immersion, and let $y : \operatorname{Spec} R \to X$ be a morphism of schemes (all in a single universe). The assertion is that there exists an ideal $J \subseteq R$ with the following property: for every commutative ring $R'$ and every ring homomorphism $\psi : R \to R'$, there exists a morphism $z : \operatorname{Spec} R' \to Z$ with $z$ followed by $\iota$ equal to $\operatorname{Spec}(\psi)$ followed by $y$ if and only if $J \subseteq \ker \psi$. Thus a single ideal of $R$ records, simultaneously for all base changes $\psi$ of the affine base, exactly when the point $y$ pulled back along $\psi$ factors through the closed subscheme $Z$; the factorisation $z$ is asserted to exist but no uniqueness claim is made. Here $\operatorname{Spec} R$ and $\operatorname{Spec} R'$ are the spectra of $R$ and $R'$ viewed as objects of the category of schemes, and $\operatorname{Spec}(\psi)$ is the induced morphism $\operatorname{Spec} R' \to \operatorname{Spec} R$.
--
--   This is the existence of the incidence (or "scheme-theoretic inverse image") ideal cutting out $y^{-1}(Z)$ inside $\operatorname{Spec} R$, in a form that is functorial in the $R$-algebra and hence usable as a representability criterion. It is used in the construction of immersions of representing objects for framed polarised abelian schemes over Noetherian bases, via [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion
    {R : Type u} [CommRing R] {X Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι]
    (y : Spec (CommRingCat.of R) ⟶ X) :
    ∃ J : Ideal R, ∀ (R' : Type u) [CommRing R'] (ψ : R →+* R'),
      (∃ z : Spec (CommRingCat.of R') ⟶ Z, z ≫ ι = Spec.map (CommRingCat.ofHom ψ) ≫ y) ↔ J ≤ RingHom.ker ψ := by sorry
